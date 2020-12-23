%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 277 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :   30
%              Number of atoms          :  149 ( 527 expanded)
%              Number of equality atoms :   97 ( 316 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10557,f40])).

fof(f40,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f10557,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f23,f10555])).

fof(f10555,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f10492,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10492,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f23,f10490])).

fof(f10490,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f10484,f6131])).

fof(f6131,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f6130])).

fof(f6130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f6103])).

fof(f6103,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f6068])).

fof(f6068,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f30,f5981])).

fof(f5981,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f5979,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f5979,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[],[f5957,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5957,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f5222,f44])).

fof(f44,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5222,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6)),k2_zfmisc_1(X7,X5)) ),
    inference(forward_demodulation,[],[f5207,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f5207,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X7),k3_xboole_0(X5,X6)),k2_zfmisc_1(X7,X5)) ),
    inference(superposition,[],[f1702,f967])).

fof(f967,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f38,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1702,plain,(
    ! [X103,X105,X102,X104] : r1_tarski(k3_xboole_0(X105,k2_zfmisc_1(X102,k3_xboole_0(X103,X104))),k2_zfmisc_1(X102,X103)) ),
    inference(superposition,[],[f381,f958])).

fof(f958,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f38,f26])).

fof(f381,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X4,k3_xboole_0(X2,X3)),X2) ),
    inference(superposition,[],[f347,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f347,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f341,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f341,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X3) ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k3_xboole_0(X2,X3),X3) ) ),
    inference(superposition,[],[f33,f327])).

fof(f327,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,X8),X8) ),
    inference(backward_demodulation,[],[f169,f326])).

fof(f326,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f294,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f294,plain,(
    ! [X10,X9] : k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X9)) = k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)) ),
    inference(superposition,[],[f28,f138])).

fof(f138,plain,(
    ! [X8,X9] : k3_xboole_0(X9,X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f137,f26])).

fof(f137,plain,(
    ! [X8,X9] : k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X8,X8)) ),
    inference(forward_demodulation,[],[f123,f35])).

fof(f123,plain,(
    ! [X8,X9] : k3_xboole_0(k3_xboole_0(X9,X8),X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f68,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f42])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f169,plain,(
    ! [X8,X9] : k4_xboole_0(k3_xboole_0(X9,X8),X8) = k4_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f141,f68])).

fof(f141,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f127,f28])).

fof(f127,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f28,f68])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10484,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f10483,f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f10483,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f10482])).

fof(f10482,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f33,f10445])).

fof(f10445,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f10402])).

fof(f10402,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f30,f10395])).

fof(f10395,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f10393,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10393,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[],[f10342,f34])).

fof(f10342,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f5262,f44])).

fof(f5262,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X0,X3)) ),
    inference(forward_demodulation,[],[f5246,f38])).

fof(f5246,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)),k2_zfmisc_1(X0,X3)) ),
    inference(superposition,[],[f2923,f958])).

fof(f2923,plain,(
    ! [X103,X101,X102,X104] : r1_tarski(k3_xboole_0(X104,k2_zfmisc_1(k3_xboole_0(X101,X103),X102)),k2_zfmisc_1(X101,X102)) ),
    inference(superposition,[],[f381,f967])).

fof(f23,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (29188)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % (29204)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (29196)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (29205)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (29197)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (29189)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (29187)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (29184)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29186)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (29204)Refutation not found, incomplete strategy% (29204)------------------------------
% 0.22/0.51  % (29204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29204)Memory used [KB]: 10618
% 0.22/0.51  % (29204)Time elapsed: 0.092 s
% 0.22/0.51  % (29204)------------------------------
% 0.22/0.51  % (29204)------------------------------
% 0.22/0.51  % (29185)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (29182)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (29208)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (29183)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (29200)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (29203)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (29195)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (29192)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (29194)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (29207)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (29210)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (29211)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (29209)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.54  % (29201)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.54  % (29198)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.54  % (29202)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (29206)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.55  % (29199)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (29190)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (29199)Refutation not found, incomplete strategy% (29199)------------------------------
% 1.42/0.55  % (29199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (29199)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (29199)Memory used [KB]: 10618
% 1.42/0.55  % (29199)Time elapsed: 0.140 s
% 1.42/0.55  % (29199)------------------------------
% 1.42/0.55  % (29199)------------------------------
% 1.42/0.55  % (29193)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (29191)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.32/0.68  % (29216)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.32/0.73  % (29218)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.59/0.83  % (29187)Time limit reached!
% 3.59/0.83  % (29187)------------------------------
% 3.59/0.83  % (29187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.83  % (29187)Termination reason: Time limit
% 3.59/0.83  
% 3.59/0.83  % (29187)Memory used [KB]: 8571
% 3.59/0.83  % (29187)Time elapsed: 0.430 s
% 3.59/0.83  % (29187)------------------------------
% 3.59/0.83  % (29187)------------------------------
% 3.82/0.91  % (29194)Time limit reached!
% 3.82/0.91  % (29194)------------------------------
% 3.82/0.91  % (29194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (29182)Time limit reached!
% 3.82/0.91  % (29182)------------------------------
% 3.82/0.91  % (29182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (29194)Termination reason: Time limit
% 3.82/0.91  
% 3.82/0.91  % (29194)Memory used [KB]: 9722
% 3.82/0.91  % (29194)Time elapsed: 0.506 s
% 3.82/0.91  % (29194)------------------------------
% 3.82/0.91  % (29194)------------------------------
% 3.82/0.91  % (29192)Time limit reached!
% 3.82/0.91  % (29192)------------------------------
% 3.82/0.91  % (29192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (29182)Termination reason: Time limit
% 3.82/0.91  % (29182)Termination phase: Saturation
% 3.82/0.91  
% 3.82/0.91  % (29182)Memory used [KB]: 5245
% 3.82/0.91  % (29182)Time elapsed: 0.500 s
% 3.82/0.91  % (29182)------------------------------
% 3.82/0.91  % (29182)------------------------------
% 3.82/0.92  % (29192)Termination reason: Time limit
% 3.82/0.92  
% 3.82/0.92  % (29192)Memory used [KB]: 16630
% 3.82/0.92  % (29192)Time elapsed: 0.507 s
% 3.82/0.92  % (29192)------------------------------
% 3.82/0.92  % (29192)------------------------------
% 4.32/0.94  % (29272)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.32/0.94  % (29183)Time limit reached!
% 4.32/0.94  % (29183)------------------------------
% 4.32/0.94  % (29183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.95  % (29183)Termination reason: Time limit
% 4.32/0.95  
% 4.32/0.95  % (29183)Memory used [KB]: 8955
% 4.32/0.95  % (29183)Time elapsed: 0.529 s
% 4.32/0.95  % (29183)------------------------------
% 4.32/0.95  % (29183)------------------------------
% 4.60/1.02  % (29189)Refutation found. Thanks to Tanya!
% 4.60/1.02  % SZS status Theorem for theBenchmark
% 4.60/1.02  % SZS output start Proof for theBenchmark
% 4.60/1.02  fof(f11135,plain,(
% 4.60/1.02    $false),
% 4.60/1.02    inference(subsumption_resolution,[],[f10557,f40])).
% 4.60/1.02  fof(f40,plain,(
% 4.60/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.60/1.02    inference(equality_resolution,[],[f31])).
% 4.60/1.02  fof(f31,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.60/1.02    inference(cnf_transformation,[],[f20])).
% 4.60/1.02  fof(f20,plain,(
% 4.60/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.60/1.02    inference(flattening,[],[f19])).
% 4.60/1.02  fof(f19,plain,(
% 4.60/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.60/1.02    inference(nnf_transformation,[],[f8])).
% 4.60/1.02  fof(f8,axiom,(
% 4.60/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 4.60/1.02  fof(f10557,plain,(
% 4.60/1.02    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 4.60/1.02    inference(backward_demodulation,[],[f23,f10555])).
% 4.60/1.02  fof(f10555,plain,(
% 4.60/1.02    k1_xboole_0 = sK0),
% 4.60/1.02    inference(subsumption_resolution,[],[f10492,f39])).
% 4.60/1.02  fof(f39,plain,(
% 4.60/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.60/1.02    inference(equality_resolution,[],[f32])).
% 4.60/1.02  fof(f32,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.60/1.02    inference(cnf_transformation,[],[f20])).
% 4.60/1.02  fof(f10492,plain,(
% 4.60/1.02    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 4.60/1.02    inference(superposition,[],[f23,f10490])).
% 4.60/1.02  fof(f10490,plain,(
% 4.60/1.02    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 4.60/1.02    inference(resolution,[],[f10484,f6131])).
% 4.60/1.02  fof(f6131,plain,(
% 4.60/1.02    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 4.60/1.02    inference(trivial_inequality_removal,[],[f6130])).
% 4.60/1.02  fof(f6130,plain,(
% 4.60/1.02    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 4.60/1.02    inference(superposition,[],[f33,f6103])).
% 4.60/1.02  fof(f6103,plain,(
% 4.60/1.02    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 4.60/1.02    inference(trivial_inequality_removal,[],[f6068])).
% 4.60/1.02  fof(f6068,plain,(
% 4.60/1.02    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 4.60/1.02    inference(superposition,[],[f30,f5981])).
% 4.60/1.02  fof(f5981,plain,(
% 4.60/1.02    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 4.60/1.02    inference(superposition,[],[f5979,f36])).
% 4.60/1.02  fof(f36,plain,(
% 4.60/1.02    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.60/1.02    inference(cnf_transformation,[],[f10])).
% 4.60/1.02  fof(f10,axiom,(
% 4.60/1.02    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 4.60/1.02  fof(f5979,plain,(
% 4.60/1.02    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 4.60/1.02    inference(resolution,[],[f5957,f34])).
% 4.60/1.02  fof(f34,plain,(
% 4.60/1.02    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 4.60/1.02    inference(cnf_transformation,[],[f21])).
% 4.60/1.02  fof(f21,plain,(
% 4.60/1.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.60/1.02    inference(nnf_transformation,[],[f2])).
% 4.60/1.02  fof(f2,axiom,(
% 4.60/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.60/1.02  fof(f5957,plain,(
% 4.60/1.02    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 4.60/1.02    inference(superposition,[],[f5222,f44])).
% 4.60/1.02  fof(f44,plain,(
% 4.60/1.02    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 4.60/1.02    inference(resolution,[],[f29,f22])).
% 4.60/1.02  fof(f22,plain,(
% 4.60/1.02    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 4.60/1.02    inference(cnf_transformation,[],[f18])).
% 4.60/1.02  fof(f18,plain,(
% 4.60/1.02    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 4.60/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).
% 4.60/1.02  fof(f17,plain,(
% 4.60/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 4.60/1.02    introduced(choice_axiom,[])).
% 4.60/1.02  fof(f15,plain,(
% 4.60/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 4.60/1.02    inference(flattening,[],[f14])).
% 4.60/1.02  fof(f14,plain,(
% 4.60/1.02    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 4.60/1.02    inference(ennf_transformation,[],[f12])).
% 4.60/1.02  fof(f12,negated_conjecture,(
% 4.60/1.02    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.60/1.02    inference(negated_conjecture,[],[f11])).
% 4.60/1.02  fof(f11,conjecture,(
% 4.60/1.02    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 4.60/1.02  fof(f29,plain,(
% 4.60/1.02    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.60/1.02    inference(cnf_transformation,[],[f16])).
% 4.60/1.02  fof(f16,plain,(
% 4.60/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.60/1.02    inference(ennf_transformation,[],[f6])).
% 4.60/1.02  fof(f6,axiom,(
% 4.60/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.60/1.02  fof(f5222,plain,(
% 4.60/1.02    ( ! [X6,X4,X7,X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6)),k2_zfmisc_1(X7,X5))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f5207,f38])).
% 4.60/1.02  fof(f38,plain,(
% 4.60/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 4.60/1.02    inference(cnf_transformation,[],[f9])).
% 4.60/1.02  fof(f9,axiom,(
% 4.60/1.02    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 4.60/1.02  fof(f5207,plain,(
% 4.60/1.02    ( ! [X6,X4,X7,X5] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X7),k3_xboole_0(X5,X6)),k2_zfmisc_1(X7,X5))) )),
% 4.60/1.02    inference(superposition,[],[f1702,f967])).
% 4.60/1.02  fof(f967,plain,(
% 4.60/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 4.60/1.02    inference(superposition,[],[f38,f26])).
% 4.60/1.02  fof(f26,plain,(
% 4.60/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.60/1.02    inference(cnf_transformation,[],[f13])).
% 4.60/1.02  fof(f13,plain,(
% 4.60/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.60/1.02    inference(rectify,[],[f1])).
% 4.60/1.02  fof(f1,axiom,(
% 4.60/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.60/1.02  fof(f1702,plain,(
% 4.60/1.02    ( ! [X103,X105,X102,X104] : (r1_tarski(k3_xboole_0(X105,k2_zfmisc_1(X102,k3_xboole_0(X103,X104))),k2_zfmisc_1(X102,X103))) )),
% 4.60/1.02    inference(superposition,[],[f381,f958])).
% 4.60/1.02  fof(f958,plain,(
% 4.60/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 4.60/1.02    inference(superposition,[],[f38,f26])).
% 4.60/1.02  fof(f381,plain,(
% 4.60/1.02    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X4,k3_xboole_0(X2,X3)),X2)) )),
% 4.60/1.02    inference(superposition,[],[f347,f42])).
% 4.60/1.02  fof(f42,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 4.60/1.02    inference(resolution,[],[f29,f27])).
% 4.60/1.02  fof(f27,plain,(
% 4.60/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.60/1.02    inference(cnf_transformation,[],[f5])).
% 4.60/1.02  fof(f5,axiom,(
% 4.60/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.60/1.02  fof(f347,plain,(
% 4.60/1.02    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X5)) )),
% 4.60/1.02    inference(superposition,[],[f341,f35])).
% 4.60/1.02  fof(f35,plain,(
% 4.60/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 4.60/1.02    inference(cnf_transformation,[],[f4])).
% 4.60/1.02  fof(f4,axiom,(
% 4.60/1.02    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 4.60/1.02  fof(f341,plain,(
% 4.60/1.02    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X3)) )),
% 4.60/1.02    inference(trivial_inequality_removal,[],[f339])).
% 4.60/1.02  fof(f339,plain,(
% 4.60/1.02    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k3_xboole_0(X2,X3),X3)) )),
% 4.60/1.02    inference(superposition,[],[f33,f327])).
% 4.60/1.02  fof(f327,plain,(
% 4.60/1.02    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,X8),X8)) )),
% 4.60/1.02    inference(backward_demodulation,[],[f169,f326])).
% 4.60/1.02  fof(f326,plain,(
% 4.60/1.02    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X9))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f294,f25])).
% 4.60/1.02  fof(f25,plain,(
% 4.60/1.02    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.60/1.02    inference(cnf_transformation,[],[f7])).
% 4.60/1.02  fof(f7,axiom,(
% 4.60/1.02    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.60/1.02  fof(f294,plain,(
% 4.60/1.02    ( ! [X10,X9] : (k4_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X9)) = k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10))) )),
% 4.60/1.02    inference(superposition,[],[f28,f138])).
% 4.60/1.02  fof(f138,plain,(
% 4.60/1.02    ( ! [X8,X9] : (k3_xboole_0(X9,X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f137,f26])).
% 4.60/1.02  fof(f137,plain,(
% 4.60/1.02    ( ! [X8,X9] : (k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X8,X8))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f123,f35])).
% 4.60/1.02  fof(f123,plain,(
% 4.60/1.02    ( ! [X8,X9] : (k3_xboole_0(k3_xboole_0(X9,X8),X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 4.60/1.02    inference(superposition,[],[f68,f68])).
% 4.60/1.02  fof(f68,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 4.60/1.02    inference(superposition,[],[f35,f42])).
% 4.60/1.02  fof(f28,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.60/1.02    inference(cnf_transformation,[],[f3])).
% 4.60/1.02  fof(f3,axiom,(
% 4.60/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.60/1.02  fof(f169,plain,(
% 4.60/1.02    ( ! [X8,X9] : (k4_xboole_0(k3_xboole_0(X9,X8),X8) = k4_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 4.60/1.02    inference(superposition,[],[f141,f68])).
% 4.60/1.02  fof(f141,plain,(
% 4.60/1.02    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f127,f28])).
% 4.60/1.02  fof(f127,plain,(
% 4.60/1.02    ( ! [X6,X5] : (k5_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 4.60/1.02    inference(superposition,[],[f28,f68])).
% 4.60/1.02  fof(f30,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 4.60/1.02    inference(cnf_transformation,[],[f20])).
% 4.60/1.02  fof(f33,plain,(
% 4.60/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 4.60/1.02    inference(cnf_transformation,[],[f21])).
% 4.60/1.02  fof(f10484,plain,(
% 4.60/1.02    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 4.60/1.02    inference(resolution,[],[f10483,f24])).
% 4.60/1.02  fof(f24,plain,(
% 4.60/1.02    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 4.60/1.02    inference(cnf_transformation,[],[f18])).
% 4.60/1.02  fof(f10483,plain,(
% 4.60/1.02    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 4.60/1.02    inference(trivial_inequality_removal,[],[f10482])).
% 4.60/1.02  fof(f10482,plain,(
% 4.60/1.02    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 4.60/1.02    inference(superposition,[],[f33,f10445])).
% 4.60/1.02  fof(f10445,plain,(
% 4.60/1.02    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 4.60/1.02    inference(trivial_inequality_removal,[],[f10402])).
% 4.60/1.02  fof(f10402,plain,(
% 4.60/1.02    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 4.60/1.02    inference(superposition,[],[f30,f10395])).
% 4.60/1.02  fof(f10395,plain,(
% 4.60/1.02    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 4.60/1.02    inference(superposition,[],[f10393,f37])).
% 4.60/1.02  fof(f37,plain,(
% 4.60/1.02    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.60/1.02    inference(cnf_transformation,[],[f10])).
% 4.60/1.02  fof(f10393,plain,(
% 4.60/1.02    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 4.60/1.02    inference(resolution,[],[f10342,f34])).
% 4.60/1.02  fof(f10342,plain,(
% 4.60/1.02    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 4.60/1.02    inference(superposition,[],[f5262,f44])).
% 4.60/1.02  fof(f5262,plain,(
% 4.60/1.02    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X0,X3))) )),
% 4.60/1.02    inference(forward_demodulation,[],[f5246,f38])).
% 4.60/1.02  fof(f5246,plain,(
% 4.60/1.02    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)),k2_zfmisc_1(X0,X3))) )),
% 4.60/1.02    inference(superposition,[],[f2923,f958])).
% 4.60/1.02  fof(f2923,plain,(
% 4.60/1.02    ( ! [X103,X101,X102,X104] : (r1_tarski(k3_xboole_0(X104,k2_zfmisc_1(k3_xboole_0(X101,X103),X102)),k2_zfmisc_1(X101,X102))) )),
% 4.60/1.02    inference(superposition,[],[f381,f967])).
% 4.60/1.02  fof(f23,plain,(
% 4.60/1.02    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 4.60/1.02    inference(cnf_transformation,[],[f18])).
% 4.60/1.02  % SZS output end Proof for theBenchmark
% 4.60/1.02  % (29189)------------------------------
% 4.60/1.02  % (29189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.02  % (29189)Termination reason: Refutation
% 4.60/1.02  
% 4.60/1.02  % (29189)Memory used [KB]: 12537
% 4.60/1.02  % (29189)Time elapsed: 0.558 s
% 4.60/1.02  % (29189)------------------------------
% 4.60/1.02  % (29189)------------------------------
% 4.60/1.03  % (29181)Success in time 0.66 s
%------------------------------------------------------------------------------
