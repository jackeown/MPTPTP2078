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
% DateTime   : Thu Dec  3 12:41:22 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 446 expanded)
%              Number of leaves         :   18 ( 140 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 663 expanded)
%              Number of equality atoms :   63 ( 401 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1613,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1612,f691])).

fof(f691,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f689,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_tarski(X0,X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f689,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f551,f37])).

fof(f37,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f551,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f290,f549])).

fof(f549,plain,(
    ! [X21,X22] : k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k4_xboole_0(X21,X22) ),
    inference(forward_demodulation,[],[f534,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f534,plain,(
    ! [X21,X22] : k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(superposition,[],[f183,f168])).

fof(f168,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f183,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f160,f65])).

fof(f65,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f45,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f160,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f56,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f290,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k5_xboole_0(X3,k2_xboole_0(X4,X3))) ),
    inference(superposition,[],[f243,f128])).

fof(f128,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f243,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f239,f45])).

fof(f239,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f76,f229])).

fof(f229,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f119,f213])).

fof(f213,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f187,f183])).

fof(f187,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f183,f45])).

fof(f119,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f76,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f1612,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1610,f690])).

fof(f690,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f688,f268])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,k2_tarski(X1,X0))
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f84,f44])).

fof(f688,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f551,f38])).

fof(f38,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f1610,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f1609,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f1609,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1608,f690])).

fof(f1608,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1607,f691])).

fof(f1607,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f1606])).

fof(f1606,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f39,f1582])).

fof(f1582,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f53,f1580])).

fof(f1580,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f1579,f549])).

fof(f1579,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f1564,f45])).

fof(f1564,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),X3) = k5_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(superposition,[],[f49,f1507])).

fof(f1507,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f1450,f214])).

fof(f214,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f187,f187])).

fof(f1450,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X1,X0),X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f136,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f136,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f51,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f39,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:56:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.45  % (11537)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (11538)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (11530)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (11535)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (11535)Refutation not found, incomplete strategy% (11535)------------------------------
% 0.21/0.47  % (11535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11535)Memory used [KB]: 10618
% 0.21/0.47  % (11535)Time elapsed: 0.047 s
% 0.21/0.47  % (11535)------------------------------
% 0.21/0.47  % (11535)------------------------------
% 0.21/0.48  % (11529)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (11527)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (11525)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (11536)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (11526)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (11533)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (11534)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (11524)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (11539)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (11532)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (11528)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (11531)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (11540)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (11541)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.54/0.58  % (11527)Refutation found. Thanks to Tanya!
% 1.54/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f1613,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(subsumption_resolution,[],[f1612,f691])).
% 1.54/0.58  fof(f691,plain,(
% 1.54/0.58    ~r2_hidden(sK0,sK2)),
% 1.54/0.58    inference(subsumption_resolution,[],[f689,f84])).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_tarski(X0,X2)) | ~r2_hidden(X0,X1)) )),
% 1.54/0.58    inference(resolution,[],[f58,f52])).
% 1.54/0.58  fof(f52,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.54/0.58    inference(ennf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.54/0.58  fof(f689,plain,(
% 1.54/0.58    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 1.54/0.58    inference(superposition,[],[f551,f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.54/0.58    inference(flattening,[],[f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.54/0.58    inference(nnf_transformation,[],[f28])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f25])).
% 1.54/0.58  fof(f25,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.54/0.58    inference(negated_conjecture,[],[f24])).
% 1.54/0.58  fof(f24,conjecture,(
% 1.54/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.54/0.60  fof(f551,plain,(
% 1.54/0.60    ( ! [X4,X3] : (r1_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 1.54/0.60    inference(backward_demodulation,[],[f290,f549])).
% 1.54/0.60  fof(f549,plain,(
% 1.54/0.60    ( ! [X21,X22] : (k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k4_xboole_0(X21,X22)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f534,f49])).
% 1.54/0.60  fof(f49,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,axiom,(
% 1.54/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.60  fof(f534,plain,(
% 1.54/0.60    ( ! [X21,X22] : (k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k5_xboole_0(X21,k3_xboole_0(X21,X22))) )),
% 1.54/0.60    inference(superposition,[],[f183,f168])).
% 1.54/0.60  fof(f168,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.54/0.60    inference(superposition,[],[f56,f51])).
% 1.54/0.60  fof(f51,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f13])).
% 1.54/0.60  fof(f13,axiom,(
% 1.54/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f11])).
% 1.54/0.60  fof(f11,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.60  fof(f183,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.54/0.60    inference(forward_demodulation,[],[f160,f65])).
% 1.54/0.60  fof(f65,plain,(
% 1.54/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.54/0.60    inference(superposition,[],[f45,f41])).
% 1.54/0.60  fof(f41,plain,(
% 1.54/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.60    inference(cnf_transformation,[],[f8])).
% 1.54/0.60  fof(f8,axiom,(
% 1.54/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.60  fof(f45,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f1])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.60  fof(f160,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(superposition,[],[f56,f40])).
% 1.54/0.60  fof(f40,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f12])).
% 1.54/0.60  fof(f12,axiom,(
% 1.54/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.54/0.60  fof(f290,plain,(
% 1.54/0.60    ( ! [X4,X3] : (r1_xboole_0(X3,k5_xboole_0(X3,k2_xboole_0(X4,X3)))) )),
% 1.54/0.60    inference(superposition,[],[f243,f128])).
% 1.54/0.60  fof(f128,plain,(
% 1.54/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.54/0.60    inference(superposition,[],[f81,f48])).
% 1.54/0.60  fof(f48,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f21])).
% 1.54/0.60  fof(f21,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.54/0.60  fof(f81,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.54/0.60    inference(superposition,[],[f48,f44])).
% 1.54/0.60  fof(f44,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f14])).
% 1.54/0.60  fof(f14,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.54/0.60  fof(f243,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 1.54/0.60    inference(forward_demodulation,[],[f239,f45])).
% 1.54/0.60  fof(f239,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,X1),X0))) )),
% 1.54/0.60    inference(superposition,[],[f76,f229])).
% 1.54/0.60  fof(f229,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 1.54/0.60    inference(backward_demodulation,[],[f119,f213])).
% 1.54/0.60  fof(f213,plain,(
% 1.54/0.60    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 1.54/0.60    inference(superposition,[],[f187,f183])).
% 1.54/0.60  fof(f187,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.54/0.60    inference(superposition,[],[f183,f45])).
% 1.54/0.60  fof(f119,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) )),
% 1.54/0.60    inference(superposition,[],[f51,f50])).
% 1.54/0.60  fof(f50,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f9])).
% 1.54/0.60  fof(f9,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.54/0.60  fof(f76,plain,(
% 1.54/0.60    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 1.54/0.60    inference(superposition,[],[f46,f45])).
% 1.54/0.60  fof(f46,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f5])).
% 1.54/0.60  fof(f5,axiom,(
% 1.54/0.60    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.54/0.60  fof(f1612,plain,(
% 1.54/0.60    r2_hidden(sK0,sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f1610,f690])).
% 1.54/0.60  fof(f690,plain,(
% 1.54/0.60    ~r2_hidden(sK1,sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f688,f268])).
% 1.54/0.60  fof(f268,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k2_tarski(X1,X0)) | ~r2_hidden(X0,X2)) )),
% 1.54/0.60    inference(superposition,[],[f84,f44])).
% 1.54/0.60  fof(f688,plain,(
% 1.54/0.60    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 1.54/0.60    inference(superposition,[],[f551,f38])).
% 1.54/0.60  fof(f38,plain,(
% 1.54/0.60    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f36])).
% 1.54/0.60  fof(f1610,plain,(
% 1.54/0.60    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.54/0.60    inference(resolution,[],[f1609,f57])).
% 1.54/0.60  fof(f57,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f31])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.54/0.60    inference(ennf_transformation,[],[f23])).
% 1.54/0.60  fof(f23,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.54/0.60  fof(f1609,plain,(
% 1.54/0.60    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f1608,f690])).
% 1.54/0.60  fof(f1608,plain,(
% 1.54/0.60    r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f1607,f691])).
% 1.54/0.60  fof(f1607,plain,(
% 1.54/0.60    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.54/0.60    inference(trivial_inequality_removal,[],[f1606])).
% 1.54/0.60  fof(f1606,plain,(
% 1.54/0.60    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.54/0.60    inference(superposition,[],[f39,f1582])).
% 1.54/0.60  fof(f1582,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.54/0.60    inference(backward_demodulation,[],[f53,f1580])).
% 1.54/0.60  fof(f1580,plain,(
% 1.54/0.60    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f1579,f549])).
% 1.54/0.60  fof(f1579,plain,(
% 1.54/0.60    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f1564,f45])).
% 1.54/0.60  fof(f1564,plain,(
% 1.54/0.60    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),X3) = k5_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.54/0.60    inference(superposition,[],[f49,f1507])).
% 1.54/0.60  fof(f1507,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0) )),
% 1.54/0.60    inference(forward_demodulation,[],[f1450,f214])).
% 1.54/0.60  fof(f214,plain,(
% 1.54/0.60    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 1.54/0.60    inference(superposition,[],[f187,f187])).
% 1.54/0.60  fof(f1450,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X1,X0),X0),k2_xboole_0(X1,X0))) )),
% 1.54/0.60    inference(superposition,[],[f136,f43])).
% 1.54/0.60  fof(f43,plain,(
% 1.54/0.60    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.54/0.60    inference(cnf_transformation,[],[f27])).
% 1.54/0.60  fof(f27,plain,(
% 1.54/0.60    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.60    inference(rectify,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.54/0.60  fof(f136,plain,(
% 1.54/0.60    ( ! [X4,X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 1.54/0.60    inference(superposition,[],[f51,f55])).
% 1.54/0.60  fof(f55,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f7])).
% 1.54/0.60  fof(f7,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f30])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.54/0.60    inference(ennf_transformation,[],[f10])).
% 1.54/0.60  fof(f10,axiom,(
% 1.54/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.54/0.60  fof(f39,plain,(
% 1.54/0.60    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f36])).
% 1.54/0.60  % SZS output end Proof for theBenchmark
% 1.54/0.60  % (11527)------------------------------
% 1.54/0.60  % (11527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (11527)Termination reason: Refutation
% 1.54/0.60  
% 1.54/0.60  % (11527)Memory used [KB]: 3454
% 1.54/0.60  % (11527)Time elapsed: 0.148 s
% 1.54/0.60  % (11527)------------------------------
% 1.54/0.60  % (11527)------------------------------
% 1.54/0.60  % (11523)Success in time 0.237 s
%------------------------------------------------------------------------------
