%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:04 EST 2020

% Result     : Theorem 5.78s
% Output     : Refutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 466 expanded)
%              Number of leaves         :   12 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          :  174 (1502 expanded)
%              Number of equality atoms :   72 ( 431 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8277,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f8271])).

fof(f8271,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2) ),
    inference(superposition,[],[f30,f8231])).

fof(f8231,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f8206,f356])).

fof(f356,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k2_relat_1(sK1))) ),
    inference(superposition,[],[f340,f42])).

fof(f42,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
            & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
          & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
        & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
        & v1_relat_1(X2) )
   => ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
      & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f340,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f333,f47])).

fof(f47,plain,(
    ! [X6] : k7_relat_1(sK2,X6) = k5_relat_1(k6_relat_1(X6),sK2) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f333,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),sK2)) ),
    inference(resolution,[],[f189,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f189,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(k5_relat_1(sK1,X12),sK2) = k5_relat_1(sK1,k5_relat_1(X12,sK2)) ) ),
    inference(resolution,[],[f138,f27])).

fof(f138,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(X15,X16),sK2) = k5_relat_1(X15,k5_relat_1(X16,sK2)) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f8206,plain,(
    k5_relat_1(sK1,k7_relat_1(sK2,sK0)) = k5_relat_1(sK1,k7_relat_1(sK2,k2_relat_1(sK1))) ),
    inference(superposition,[],[f8179,f2586])).

fof(f2586,plain,(
    k7_relat_1(sK2,k2_relat_1(sK1)) = k7_relat_1(sK2,k3_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(superposition,[],[f67,f2577])).

fof(f2577,plain,(
    k2_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(resolution,[],[f1579,f57])).

fof(f57,plain,(
    r1_tarski(k2_relat_1(sK1),k3_xboole_0(k1_relat_1(sK2),sK0)) ),
    inference(backward_demodulation,[],[f29,f56])).

fof(f56,plain,(
    ! [X6] : k3_xboole_0(k1_relat_1(sK2),X6) = k1_relat_1(k7_relat_1(sK2,X6)) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f29,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f1579,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(k1_relat_1(sK2),X1))
      | k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X1,X0)) = X0 ) ),
    inference(resolution,[],[f115,f70])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f51,f28])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | v1_relat_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f115,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2))
      | k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X2,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f86,f114])).

fof(f114,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f110,f56])).

fof(f110,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f76,f98])).

fof(f98,plain,(
    ! [X15,X16] : k7_relat_1(k7_relat_1(sK2,X15),X16) = k7_relat_1(sK2,k3_xboole_0(X15,X16)) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f76,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) ),
    inference(forward_demodulation,[],[f72,f56])).

fof(f72,plain,(
    ! [X2,X3] : k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X2)),X3) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) ),
    inference(resolution,[],[f70,f35])).

fof(f86,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = X3
      | ~ r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2))
      | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    inference(forward_demodulation,[],[f84,f76])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2))
      | k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = X3
      | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    inference(superposition,[],[f37,f56])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f67,plain,(
    ! [X8] : k7_relat_1(sK2,X8) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X8)) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f8179,plain,(
    ! [X1] : k5_relat_1(sK1,k7_relat_1(sK2,X1)) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X1,k2_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f8154,f340])).

fof(f8154,plain,(
    ! [X1] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X1)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X1,k2_relat_1(sK1)))) ),
    inference(superposition,[],[f823,f1669])).

fof(f1669,plain,(
    ! [X0] : k5_relat_1(sK1,k6_relat_1(X0)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X0),k2_relat_1(sK1))) ),
    inference(superposition,[],[f1164,f42])).

fof(f1164,plain,(
    ! [X21,X22] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X21)),k6_relat_1(X22)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X22),X21)) ),
    inference(forward_demodulation,[],[f1155,f45])).

fof(f45,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X3)) ),
    inference(resolution,[],[f34,f31])).

fof(f1155,plain,(
    ! [X21,X22] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X21)),k6_relat_1(X22)) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X21),k6_relat_1(X22))) ),
    inference(resolution,[],[f354,f31])).

fof(f354,plain,(
    ! [X28,X27] :
      ( ~ v1_relat_1(X27)
      | k5_relat_1(k5_relat_1(sK1,X27),k6_relat_1(X28)) = k5_relat_1(sK1,k5_relat_1(X27,k6_relat_1(X28))) ) ),
    inference(resolution,[],[f134,f27])).

fof(f134,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) ) ),
    inference(resolution,[],[f33,f31])).

fof(f823,plain,(
    ! [X6,X5] : k5_relat_1(k5_relat_1(sK1,k7_relat_1(k6_relat_1(X5),X6)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f336,f821])).

fof(f821,plain,(
    ! [X15,X16] : k7_relat_1(sK2,k3_xboole_0(X16,X15)) = k5_relat_1(k7_relat_1(k6_relat_1(X16),X15),sK2) ),
    inference(forward_demodulation,[],[f820,f45])).

fof(f820,plain,(
    ! [X15,X16] : k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k7_relat_1(sK2,k3_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f819,f109])).

fof(f109,plain,(
    ! [X4,X5] : k5_relat_1(k6_relat_1(X5),k7_relat_1(sK2,X4)) = k7_relat_1(sK2,k3_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f73,f98])).

fof(f73,plain,(
    ! [X4,X5] : k7_relat_1(k7_relat_1(sK2,X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(sK2,X4)) ),
    inference(resolution,[],[f70,f34])).

fof(f819,plain,(
    ! [X15,X16] : k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k5_relat_1(k6_relat_1(X15),k7_relat_1(sK2,X16)) ),
    inference(forward_demodulation,[],[f753,f47])).

fof(f753,plain,(
    ! [X15,X16] : k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k5_relat_1(k6_relat_1(X15),k5_relat_1(k6_relat_1(X16),sK2)) ),
    inference(resolution,[],[f185,f31])).

fof(f185,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(k6_relat_1(X4),X3),sK2) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X3,sK2)) ) ),
    inference(resolution,[],[f138,f31])).

fof(f336,plain,(
    ! [X6,X5] : k5_relat_1(k5_relat_1(sK1,k7_relat_1(k6_relat_1(X5),X6)),sK2) = k5_relat_1(sK1,k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),sK2)) ),
    inference(resolution,[],[f189,f156])).

fof(f156,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f149,f31])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f90,f31])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(superposition,[],[f38,f45])).

fof(f30,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (19533)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.45  % (19525)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (19519)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (19518)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (19523)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (19537)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (19515)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (19516)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (19517)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (19529)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (19535)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (19522)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (19534)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (19521)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (19520)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (19526)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (19531)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (19524)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (19538)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (19538)Refutation not found, incomplete strategy% (19538)------------------------------
% 0.21/0.51  % (19538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19538)Memory used [KB]: 10618
% 0.21/0.51  % (19538)Time elapsed: 0.106 s
% 0.21/0.51  % (19538)------------------------------
% 0.21/0.51  % (19538)------------------------------
% 0.21/0.52  % (19527)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (19518)Refutation not found, incomplete strategy% (19518)------------------------------
% 0.21/0.52  % (19518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19518)Memory used [KB]: 10490
% 0.21/0.52  % (19518)Time elapsed: 0.101 s
% 0.21/0.52  % (19518)------------------------------
% 0.21/0.52  % (19518)------------------------------
% 0.21/0.52  % (19532)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (19536)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (19528)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.54  % (19530)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.89/0.60  % (19537)Refutation not found, incomplete strategy% (19537)------------------------------
% 1.89/0.60  % (19537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.60  % (19537)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.60  
% 1.89/0.60  % (19537)Memory used [KB]: 1663
% 1.89/0.60  % (19537)Time elapsed: 0.157 s
% 1.89/0.60  % (19537)------------------------------
% 1.89/0.60  % (19537)------------------------------
% 4.23/0.91  % (19527)Time limit reached!
% 4.23/0.91  % (19527)------------------------------
% 4.23/0.91  % (19527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.92  % (19522)Time limit reached!
% 4.41/0.92  % (19522)------------------------------
% 4.41/0.92  % (19522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/0.93  % (19522)Termination reason: Time limit
% 4.55/0.93  % (19522)Termination phase: Saturation
% 4.55/0.93  
% 4.55/0.93  % (19522)Memory used [KB]: 17014
% 4.55/0.93  % (19522)Time elapsed: 0.500 s
% 4.55/0.93  % (19522)------------------------------
% 4.55/0.93  % (19522)------------------------------
% 4.55/0.93  % (19527)Termination reason: Time limit
% 4.55/0.93  
% 4.55/0.93  % (19527)Memory used [KB]: 16247
% 4.55/0.93  % (19527)Time elapsed: 0.512 s
% 4.55/0.93  % (19527)------------------------------
% 4.55/0.93  % (19527)------------------------------
% 5.78/1.11  % (19524)Refutation found. Thanks to Tanya!
% 5.78/1.11  % SZS status Theorem for theBenchmark
% 5.78/1.11  % SZS output start Proof for theBenchmark
% 5.78/1.11  fof(f8277,plain,(
% 5.78/1.11    $false),
% 5.78/1.11    inference(trivial_inequality_removal,[],[f8271])).
% 5.78/1.11  fof(f8271,plain,(
% 5.78/1.11    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,sK2)),
% 5.78/1.11    inference(superposition,[],[f30,f8231])).
% 5.78/1.11  fof(f8231,plain,(
% 5.78/1.11    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 5.78/1.11    inference(forward_demodulation,[],[f8206,f356])).
% 5.78/1.11  fof(f356,plain,(
% 5.78/1.11    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k2_relat_1(sK1)))),
% 5.78/1.11    inference(superposition,[],[f340,f42])).
% 5.78/1.11  fof(f42,plain,(
% 5.78/1.11    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 5.78/1.11    inference(resolution,[],[f32,f27])).
% 5.78/1.11  fof(f27,plain,(
% 5.78/1.11    v1_relat_1(sK1)),
% 5.78/1.11    inference(cnf_transformation,[],[f26])).
% 5.78/1.11  fof(f26,plain,(
% 5.78/1.11    (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 5.78/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24])).
% 5.78/1.11  fof(f24,plain,(
% 5.78/1.11    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 5.78/1.11    introduced(choice_axiom,[])).
% 5.78/1.12  fof(f25,plain,(
% 5.78/1.12    ? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) => (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2))),
% 5.78/1.12    introduced(choice_axiom,[])).
% 5.78/1.12  fof(f13,plain,(
% 5.78/1.12    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 5.78/1.12    inference(flattening,[],[f12])).
% 5.78/1.12  fof(f12,plain,(
% 5.78/1.12    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 5.78/1.12    inference(ennf_transformation,[],[f11])).
% 5.78/1.12  fof(f11,negated_conjecture,(
% 5.78/1.12    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 5.78/1.12    inference(negated_conjecture,[],[f10])).
% 5.78/1.12  fof(f10,conjecture,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).
% 5.78/1.12  fof(f32,plain,(
% 5.78/1.12    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 5.78/1.12    inference(cnf_transformation,[],[f14])).
% 5.78/1.12  fof(f14,plain,(
% 5.78/1.12    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 5.78/1.12    inference(ennf_transformation,[],[f6])).
% 5.78/1.12  fof(f6,axiom,(
% 5.78/1.12    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 5.78/1.12  fof(f340,plain,(
% 5.78/1.12    ( ! [X2] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X2))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f333,f47])).
% 5.78/1.12  fof(f47,plain,(
% 5.78/1.12    ( ! [X6] : (k7_relat_1(sK2,X6) = k5_relat_1(k6_relat_1(X6),sK2)) )),
% 5.78/1.12    inference(resolution,[],[f34,f28])).
% 5.78/1.12  fof(f28,plain,(
% 5.78/1.12    v1_relat_1(sK2)),
% 5.78/1.12    inference(cnf_transformation,[],[f26])).
% 5.78/1.12  fof(f34,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f16])).
% 5.78/1.12  fof(f16,plain,(
% 5.78/1.12    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 5.78/1.12    inference(ennf_transformation,[],[f9])).
% 5.78/1.12  fof(f9,axiom,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 5.78/1.12  fof(f333,plain,(
% 5.78/1.12    ( ! [X2] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),sK2))) )),
% 5.78/1.12    inference(resolution,[],[f189,f31])).
% 5.78/1.12  fof(f31,plain,(
% 5.78/1.12    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 5.78/1.12    inference(cnf_transformation,[],[f2])).
% 5.78/1.12  fof(f2,axiom,(
% 5.78/1.12    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 5.78/1.12  fof(f189,plain,(
% 5.78/1.12    ( ! [X12] : (~v1_relat_1(X12) | k5_relat_1(k5_relat_1(sK1,X12),sK2) = k5_relat_1(sK1,k5_relat_1(X12,sK2))) )),
% 5.78/1.12    inference(resolution,[],[f138,f27])).
% 5.78/1.12  fof(f138,plain,(
% 5.78/1.12    ( ! [X15,X16] : (~v1_relat_1(X15) | ~v1_relat_1(X16) | k5_relat_1(k5_relat_1(X15,X16),sK2) = k5_relat_1(X15,k5_relat_1(X16,sK2))) )),
% 5.78/1.12    inference(resolution,[],[f33,f28])).
% 5.78/1.12  fof(f33,plain,(
% 5.78/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f15])).
% 5.78/1.12  fof(f15,plain,(
% 5.78/1.12    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.78/1.12    inference(ennf_transformation,[],[f5])).
% 5.78/1.12  fof(f5,axiom,(
% 5.78/1.12    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 5.78/1.12  fof(f8206,plain,(
% 5.78/1.12    k5_relat_1(sK1,k7_relat_1(sK2,sK0)) = k5_relat_1(sK1,k7_relat_1(sK2,k2_relat_1(sK1)))),
% 5.78/1.12    inference(superposition,[],[f8179,f2586])).
% 5.78/1.12  fof(f2586,plain,(
% 5.78/1.12    k7_relat_1(sK2,k2_relat_1(sK1)) = k7_relat_1(sK2,k3_xboole_0(sK0,k2_relat_1(sK1)))),
% 5.78/1.12    inference(superposition,[],[f67,f2577])).
% 5.78/1.12  fof(f2577,plain,(
% 5.78/1.12    k2_relat_1(sK1) = k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(sK0,k2_relat_1(sK1)))),
% 5.78/1.12    inference(resolution,[],[f1579,f57])).
% 5.78/1.12  fof(f57,plain,(
% 5.78/1.12    r1_tarski(k2_relat_1(sK1),k3_xboole_0(k1_relat_1(sK2),sK0))),
% 5.78/1.12    inference(backward_demodulation,[],[f29,f56])).
% 5.78/1.12  fof(f56,plain,(
% 5.78/1.12    ( ! [X6] : (k3_xboole_0(k1_relat_1(sK2),X6) = k1_relat_1(k7_relat_1(sK2,X6))) )),
% 5.78/1.12    inference(resolution,[],[f35,f28])).
% 5.78/1.12  fof(f35,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 5.78/1.12    inference(cnf_transformation,[],[f17])).
% 5.78/1.12  fof(f17,plain,(
% 5.78/1.12    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 5.78/1.12    inference(ennf_transformation,[],[f7])).
% 5.78/1.12  fof(f7,axiom,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 5.78/1.12  fof(f29,plain,(
% 5.78/1.12    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 5.78/1.12    inference(cnf_transformation,[],[f26])).
% 5.78/1.12  fof(f1579,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X1,X0)) = X0) )),
% 5.78/1.12    inference(resolution,[],[f115,f70])).
% 5.78/1.12  fof(f70,plain,(
% 5.78/1.12    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 5.78/1.12    inference(resolution,[],[f69,f31])).
% 5.78/1.12  fof(f69,plain,(
% 5.78/1.12    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k7_relat_1(sK2,X0))) )),
% 5.78/1.12    inference(resolution,[],[f51,f28])).
% 5.78/1.12  fof(f51,plain,(
% 5.78/1.12    ( ! [X0] : (~v1_relat_1(sK2) | v1_relat_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 5.78/1.12    inference(superposition,[],[f38,f47])).
% 5.78/1.12  fof(f38,plain,(
% 5.78/1.12    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f22])).
% 5.78/1.12  fof(f22,plain,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 5.78/1.12    inference(flattening,[],[f21])).
% 5.78/1.12  fof(f21,plain,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 5.78/1.12    inference(ennf_transformation,[],[f1])).
% 5.78/1.12  fof(f1,axiom,(
% 5.78/1.12    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 5.78/1.12  fof(f115,plain,(
% 5.78/1.12    ( ! [X2,X3] : (~v1_relat_1(k7_relat_1(sK2,X2)) | ~r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2)) | k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X2,X3)) = X3) )),
% 5.78/1.12    inference(backward_demodulation,[],[f86,f114])).
% 5.78/1.12  fof(f114,plain,(
% 5.78/1.12    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = k3_xboole_0(k1_relat_1(sK2),k3_xboole_0(X2,X3))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f110,f56])).
% 5.78/1.12  fof(f110,plain,(
% 5.78/1.12    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X2,X3)))) )),
% 5.78/1.12    inference(backward_demodulation,[],[f76,f98])).
% 5.78/1.12  fof(f98,plain,(
% 5.78/1.12    ( ! [X15,X16] : (k7_relat_1(k7_relat_1(sK2,X15),X16) = k7_relat_1(sK2,k3_xboole_0(X15,X16))) )),
% 5.78/1.12    inference(resolution,[],[f39,f28])).
% 5.78/1.12  fof(f39,plain,(
% 5.78/1.12    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 5.78/1.12    inference(cnf_transformation,[],[f23])).
% 5.78/1.12  fof(f23,plain,(
% 5.78/1.12    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 5.78/1.12    inference(ennf_transformation,[],[f3])).
% 5.78/1.12  fof(f3,axiom,(
% 5.78/1.12    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 5.78/1.12  fof(f76,plain,(
% 5.78/1.12    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3)) )),
% 5.78/1.12    inference(forward_demodulation,[],[f72,f56])).
% 5.78/1.12  fof(f72,plain,(
% 5.78/1.12    ( ! [X2,X3] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X2)),X3) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3))) )),
% 5.78/1.12    inference(resolution,[],[f70,f35])).
% 5.78/1.12  fof(f86,plain,(
% 5.78/1.12    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(k1_relat_1(sK2),X2),X3) = X3 | ~r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2)) | ~v1_relat_1(k7_relat_1(sK2,X2))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f84,f76])).
% 5.78/1.12  fof(f84,plain,(
% 5.78/1.12    ( ! [X2,X3] : (~r1_tarski(X3,k3_xboole_0(k1_relat_1(sK2),X2)) | k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3)) = X3 | ~v1_relat_1(k7_relat_1(sK2,X2))) )),
% 5.78/1.12    inference(superposition,[],[f37,f56])).
% 5.78/1.12  fof(f37,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 5.78/1.12    inference(cnf_transformation,[],[f20])).
% 5.78/1.12  fof(f20,plain,(
% 5.78/1.12    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.78/1.12    inference(flattening,[],[f19])).
% 5.78/1.12  fof(f19,plain,(
% 5.78/1.12    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.78/1.12    inference(ennf_transformation,[],[f8])).
% 5.78/1.12  fof(f8,axiom,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 5.78/1.12  fof(f67,plain,(
% 5.78/1.12    ( ! [X8] : (k7_relat_1(sK2,X8) = k7_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X8))) )),
% 5.78/1.12    inference(resolution,[],[f36,f28])).
% 5.78/1.12  fof(f36,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 5.78/1.12    inference(cnf_transformation,[],[f18])).
% 5.78/1.12  fof(f18,plain,(
% 5.78/1.12    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 5.78/1.12    inference(ennf_transformation,[],[f4])).
% 5.78/1.12  fof(f4,axiom,(
% 5.78/1.12    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 5.78/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 5.78/1.12  fof(f8179,plain,(
% 5.78/1.12    ( ! [X1] : (k5_relat_1(sK1,k7_relat_1(sK2,X1)) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X1,k2_relat_1(sK1))))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f8154,f340])).
% 5.78/1.12  fof(f8154,plain,(
% 5.78/1.12    ( ! [X1] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X1)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X1,k2_relat_1(sK1))))) )),
% 5.78/1.12    inference(superposition,[],[f823,f1669])).
% 5.78/1.12  fof(f1669,plain,(
% 5.78/1.12    ( ! [X0] : (k5_relat_1(sK1,k6_relat_1(X0)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X0),k2_relat_1(sK1)))) )),
% 5.78/1.12    inference(superposition,[],[f1164,f42])).
% 5.78/1.12  fof(f1164,plain,(
% 5.78/1.12    ( ! [X21,X22] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X21)),k6_relat_1(X22)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X22),X21))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f1155,f45])).
% 5.78/1.12  fof(f45,plain,(
% 5.78/1.12    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X3))) )),
% 5.78/1.12    inference(resolution,[],[f34,f31])).
% 5.78/1.12  fof(f1155,plain,(
% 5.78/1.12    ( ! [X21,X22] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X21)),k6_relat_1(X22)) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X21),k6_relat_1(X22)))) )),
% 5.78/1.12    inference(resolution,[],[f354,f31])).
% 5.78/1.12  fof(f354,plain,(
% 5.78/1.12    ( ! [X28,X27] : (~v1_relat_1(X27) | k5_relat_1(k5_relat_1(sK1,X27),k6_relat_1(X28)) = k5_relat_1(sK1,k5_relat_1(X27,k6_relat_1(X28)))) )),
% 5.78/1.12    inference(resolution,[],[f134,f27])).
% 5.78/1.12  fof(f134,plain,(
% 5.78/1.12    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | ~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6)))) )),
% 5.78/1.12    inference(resolution,[],[f33,f31])).
% 5.78/1.12  fof(f823,plain,(
% 5.78/1.12    ( ! [X6,X5] : (k5_relat_1(k5_relat_1(sK1,k7_relat_1(k6_relat_1(X5),X6)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,k3_xboole_0(X5,X6)))) )),
% 5.78/1.12    inference(backward_demodulation,[],[f336,f821])).
% 5.78/1.12  fof(f821,plain,(
% 5.78/1.12    ( ! [X15,X16] : (k7_relat_1(sK2,k3_xboole_0(X16,X15)) = k5_relat_1(k7_relat_1(k6_relat_1(X16),X15),sK2)) )),
% 5.78/1.12    inference(forward_demodulation,[],[f820,f45])).
% 5.78/1.12  fof(f820,plain,(
% 5.78/1.12    ( ! [X15,X16] : (k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k7_relat_1(sK2,k3_xboole_0(X16,X15))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f819,f109])).
% 5.78/1.12  fof(f109,plain,(
% 5.78/1.12    ( ! [X4,X5] : (k5_relat_1(k6_relat_1(X5),k7_relat_1(sK2,X4)) = k7_relat_1(sK2,k3_xboole_0(X4,X5))) )),
% 5.78/1.12    inference(backward_demodulation,[],[f73,f98])).
% 5.78/1.12  fof(f73,plain,(
% 5.78/1.12    ( ! [X4,X5] : (k7_relat_1(k7_relat_1(sK2,X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(sK2,X4))) )),
% 5.78/1.12    inference(resolution,[],[f70,f34])).
% 5.78/1.12  fof(f819,plain,(
% 5.78/1.12    ( ! [X15,X16] : (k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k5_relat_1(k6_relat_1(X15),k7_relat_1(sK2,X16))) )),
% 5.78/1.12    inference(forward_demodulation,[],[f753,f47])).
% 5.78/1.12  fof(f753,plain,(
% 5.78/1.12    ( ! [X15,X16] : (k5_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)),sK2) = k5_relat_1(k6_relat_1(X15),k5_relat_1(k6_relat_1(X16),sK2))) )),
% 5.78/1.12    inference(resolution,[],[f185,f31])).
% 5.78/1.12  fof(f185,plain,(
% 5.78/1.12    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(k6_relat_1(X4),X3),sK2) = k5_relat_1(k6_relat_1(X4),k5_relat_1(X3,sK2))) )),
% 5.78/1.12    inference(resolution,[],[f138,f31])).
% 5.78/1.12  fof(f336,plain,(
% 5.78/1.12    ( ! [X6,X5] : (k5_relat_1(k5_relat_1(sK1,k7_relat_1(k6_relat_1(X5),X6)),sK2) = k5_relat_1(sK1,k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),sK2))) )),
% 5.78/1.12    inference(resolution,[],[f189,f156])).
% 5.78/1.12  fof(f156,plain,(
% 5.78/1.12    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 5.78/1.12    inference(resolution,[],[f149,f31])).
% 5.78/1.12  fof(f149,plain,(
% 5.78/1.12    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 5.78/1.12    inference(resolution,[],[f90,f31])).
% 5.78/1.12  fof(f90,plain,(
% 5.78/1.12    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X2)) | v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 5.78/1.12    inference(superposition,[],[f38,f45])).
% 5.78/1.12  fof(f30,plain,(
% 5.78/1.12    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 5.78/1.12    inference(cnf_transformation,[],[f26])).
% 5.78/1.12  % SZS output end Proof for theBenchmark
% 5.78/1.12  % (19524)------------------------------
% 5.78/1.12  % (19524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.78/1.12  % (19524)Termination reason: Refutation
% 5.78/1.12  
% 5.78/1.12  % (19524)Memory used [KB]: 10106
% 5.78/1.12  % (19524)Time elapsed: 0.712 s
% 5.78/1.12  % (19524)------------------------------
% 5.78/1.12  % (19524)------------------------------
% 5.78/1.12  % (19514)Success in time 0.759 s
%------------------------------------------------------------------------------
