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
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   99 (1351 expanded)
%              Number of leaves         :   21 ( 417 expanded)
%              Depth                    :   25
%              Number of atoms          :  202 (3131 expanded)
%              Number of equality atoms :  128 (2120 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1810,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1809,f1807])).

fof(f1807,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f1755,f1800])).

fof(f1800,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1745,f1755])).

fof(f1745,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f1700,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1700,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f1563])).

fof(f1563,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f1544,f476])).

fof(f476,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f260,f452])).

fof(f452,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f368,f46])).

fof(f46,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).

fof(f32,plain,
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

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f368,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f260,f263])).

fof(f263,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f245,f114])).

fof(f114,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f63,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f245,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f73,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f260,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f236,f96])).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f59,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f236,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f73,f189])).

fof(f189,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f113,f188])).

fof(f188,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f185,f121])).

fof(f121,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f116,f51])).

fof(f116,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f63,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f58,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f185,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f62,f183])).

fof(f183,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f182,f119])).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f112,f51])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f63,f50])).

fof(f182,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(resolution,[],[f157,f84])).

fof(f84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f78,f83])).

fof(f83,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f53,f78])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f78,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f44])).

fof(f44,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f157,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | k2_xboole_0(X1,k4_xboole_0(X2,X1)) = X2 ) ),
    inference(resolution,[],[f65,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f113,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f63,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1544,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f1464,f63])).

fof(f1464,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) ),
    inference(superposition,[],[f195,f73])).

fof(f195,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f64,f59])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1755,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f48,f1754])).

fof(f1754,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f47,f227,f234,f1745])).

fof(f234,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f49,f227])).

fof(f49,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f227,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f69,f86])).

fof(f86,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f46])).

fof(f47,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f1809,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1808,f1800])).

fof(f1808,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1756,f183])).

fof(f1756,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f46,f1754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (20882)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.48  % (20906)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.49  % (20898)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (20890)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (20892)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (20877)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (20892)Refutation not found, incomplete strategy% (20892)------------------------------
% 0.20/0.50  % (20892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20894)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (20900)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (20892)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20892)Memory used [KB]: 6140
% 0.20/0.51  % (20892)Time elapsed: 0.003 s
% 0.20/0.51  % (20892)------------------------------
% 0.20/0.51  % (20892)------------------------------
% 0.20/0.51  % (20881)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (20884)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (20902)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (20893)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (20883)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (20886)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (20885)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (20879)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (20878)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20880)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (20891)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (20901)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (20894)Refutation not found, incomplete strategy% (20894)------------------------------
% 0.20/0.53  % (20894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20894)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20894)Memory used [KB]: 10618
% 0.20/0.53  % (20894)Time elapsed: 0.124 s
% 0.20/0.53  % (20894)------------------------------
% 0.20/0.53  % (20894)------------------------------
% 0.20/0.53  % (20895)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (20899)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (20904)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (20905)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (20903)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (20896)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (20888)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (20897)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (20887)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (20889)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (20888)Refutation not found, incomplete strategy% (20888)------------------------------
% 0.20/0.55  % (20888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20888)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20888)Memory used [KB]: 10618
% 0.20/0.55  % (20888)Time elapsed: 0.150 s
% 0.20/0.55  % (20888)------------------------------
% 0.20/0.55  % (20888)------------------------------
% 0.20/0.55  % (20887)Refutation not found, incomplete strategy% (20887)------------------------------
% 0.20/0.55  % (20887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20887)Memory used [KB]: 10618
% 0.20/0.55  % (20887)Time elapsed: 0.149 s
% 0.20/0.55  % (20887)------------------------------
% 0.20/0.55  % (20887)------------------------------
% 1.54/0.56  % (20897)Refutation not found, incomplete strategy% (20897)------------------------------
% 1.54/0.56  % (20897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (20897)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (20897)Memory used [KB]: 10874
% 1.54/0.57  % (20897)Time elapsed: 0.164 s
% 1.54/0.57  % (20897)------------------------------
% 1.54/0.57  % (20897)------------------------------
% 1.67/0.62  % (20884)Refutation found. Thanks to Tanya!
% 1.67/0.62  % SZS status Theorem for theBenchmark
% 2.08/0.64  % SZS output start Proof for theBenchmark
% 2.08/0.64  fof(f1810,plain,(
% 2.08/0.64    $false),
% 2.08/0.64    inference(subsumption_resolution,[],[f1809,f1807])).
% 2.08/0.64  fof(f1807,plain,(
% 2.08/0.64    k1_xboole_0 != k1_tarski(sK0)),
% 2.08/0.64    inference(backward_demodulation,[],[f1755,f1800])).
% 2.08/0.64  fof(f1800,plain,(
% 2.08/0.64    k1_xboole_0 = sK2),
% 2.08/0.64    inference(subsumption_resolution,[],[f1745,f1755])).
% 2.08/0.64  fof(f1745,plain,(
% 2.08/0.64    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 2.08/0.64    inference(resolution,[],[f1700,f69])).
% 2.08/0.64  fof(f69,plain,(
% 2.08/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f43])).
% 2.08/0.64  fof(f43,plain,(
% 2.08/0.64    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.08/0.64    inference(flattening,[],[f42])).
% 2.08/0.64  fof(f42,plain,(
% 2.08/0.64    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.08/0.64    inference(nnf_transformation,[],[f23])).
% 2.08/0.64  fof(f23,axiom,(
% 2.08/0.64    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.08/0.64  fof(f1700,plain,(
% 2.08/0.64    r1_tarski(sK2,k1_tarski(sK0))),
% 2.08/0.64    inference(superposition,[],[f57,f1563])).
% 2.08/0.64  fof(f1563,plain,(
% 2.08/0.64    k1_tarski(sK0) = k2_xboole_0(sK2,sK1)),
% 2.08/0.64    inference(superposition,[],[f1544,f476])).
% 2.08/0.64  fof(f476,plain,(
% 2.08/0.64    k1_tarski(sK0) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))),
% 2.08/0.64    inference(superposition,[],[f260,f452])).
% 2.08/0.64  fof(f452,plain,(
% 2.08/0.64    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 2.08/0.64    inference(superposition,[],[f368,f46])).
% 2.08/0.64  fof(f46,plain,(
% 2.08/0.64    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.08/0.64    inference(cnf_transformation,[],[f33])).
% 2.08/0.64  fof(f33,plain,(
% 2.08/0.64    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f32])).
% 2.08/0.64  fof(f32,plain,(
% 2.08/0.64    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f28,plain,(
% 2.08/0.64    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.64    inference(ennf_transformation,[],[f26])).
% 2.08/0.64  fof(f26,negated_conjecture,(
% 2.08/0.64    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.64    inference(negated_conjecture,[],[f25])).
% 2.08/0.64  fof(f25,conjecture,(
% 2.08/0.64    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.08/0.64  fof(f368,plain,(
% 2.08/0.64    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10))) )),
% 2.08/0.64    inference(superposition,[],[f260,f263])).
% 2.08/0.64  fof(f263,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.08/0.64    inference(forward_demodulation,[],[f245,f114])).
% 2.08/0.64  fof(f114,plain,(
% 2.08/0.64    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 2.08/0.64    inference(superposition,[],[f63,f58])).
% 2.08/0.64  fof(f58,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f1])).
% 2.08/0.64  fof(f1,axiom,(
% 2.08/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.08/0.64  fof(f63,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f8])).
% 2.08/0.64  fof(f8,axiom,(
% 2.08/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.08/0.64  fof(f245,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 2.08/0.64    inference(superposition,[],[f73,f64])).
% 2.08/0.64  fof(f64,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f15])).
% 2.08/0.64  fof(f15,axiom,(
% 2.08/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.08/0.64  fof(f73,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f14])).
% 2.08/0.64  fof(f14,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.08/0.64  fof(f260,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.08/0.64    inference(forward_demodulation,[],[f236,f96])).
% 2.08/0.64  fof(f96,plain,(
% 2.08/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.08/0.64    inference(superposition,[],[f59,f51])).
% 2.08/0.64  fof(f51,plain,(
% 2.08/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f12])).
% 2.08/0.64  fof(f12,axiom,(
% 2.08/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.08/0.64  fof(f59,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f2])).
% 2.08/0.64  fof(f2,axiom,(
% 2.08/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.08/0.64  fof(f236,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(superposition,[],[f73,f189])).
% 2.08/0.64  fof(f189,plain,(
% 2.08/0.64    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.08/0.64    inference(backward_demodulation,[],[f113,f188])).
% 2.08/0.64  fof(f188,plain,(
% 2.08/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.08/0.64    inference(forward_demodulation,[],[f185,f121])).
% 2.08/0.64  fof(f121,plain,(
% 2.08/0.64    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 2.08/0.64    inference(forward_demodulation,[],[f116,f51])).
% 2.08/0.64  fof(f116,plain,(
% 2.08/0.64    ( ! [X6] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X6)) )),
% 2.08/0.64    inference(superposition,[],[f63,f88])).
% 2.08/0.64  fof(f88,plain,(
% 2.08/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.08/0.64    inference(superposition,[],[f58,f50])).
% 2.08/0.64  fof(f50,plain,(
% 2.08/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f9])).
% 2.08/0.64  fof(f9,axiom,(
% 2.08/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.08/0.64  fof(f185,plain,(
% 2.08/0.64    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.08/0.64    inference(superposition,[],[f62,f183])).
% 2.08/0.64  fof(f183,plain,(
% 2.08/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.08/0.64    inference(forward_demodulation,[],[f182,f119])).
% 2.08/0.64  fof(f119,plain,(
% 2.08/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.64    inference(forward_demodulation,[],[f112,f51])).
% 2.08/0.64  fof(f112,plain,(
% 2.08/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.64    inference(superposition,[],[f63,f50])).
% 2.08/0.64  fof(f182,plain,(
% 2.08/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.08/0.64    inference(resolution,[],[f157,f84])).
% 2.08/0.64  fof(f84,plain,(
% 2.08/0.64    v1_xboole_0(k1_xboole_0)),
% 2.08/0.64    inference(backward_demodulation,[],[f78,f83])).
% 2.08/0.64  fof(f83,plain,(
% 2.08/0.64    k1_xboole_0 = sK5),
% 2.08/0.64    inference(resolution,[],[f53,f78])).
% 2.08/0.64  fof(f53,plain,(
% 2.08/0.64    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f29])).
% 2.08/0.64  fof(f29,plain,(
% 2.08/0.64    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.08/0.64    inference(ennf_transformation,[],[f6])).
% 2.08/0.64  fof(f6,axiom,(
% 2.08/0.64    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.08/0.64  fof(f78,plain,(
% 2.08/0.64    v1_xboole_0(sK5)),
% 2.08/0.64    inference(cnf_transformation,[],[f45])).
% 2.08/0.64  fof(f45,plain,(
% 2.08/0.64    v1_xboole_0(sK5)),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f44])).
% 2.08/0.64  fof(f44,plain,(
% 2.08/0.64    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK5)),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f7,axiom,(
% 2.08/0.64    ? [X0] : v1_xboole_0(X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 2.08/0.64  fof(f157,plain,(
% 2.08/0.64    ( ! [X2,X1] : (~v1_xboole_0(X1) | k2_xboole_0(X1,k4_xboole_0(X2,X1)) = X2) )),
% 2.08/0.64    inference(resolution,[],[f65,f107])).
% 2.08/0.64  fof(f107,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.08/0.64    inference(resolution,[],[f67,f54])).
% 2.08/0.64  fof(f54,plain,(
% 2.08/0.64    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f37])).
% 2.08/0.64  fof(f37,plain,(
% 2.08/0.64    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 2.08/0.64  fof(f36,plain,(
% 2.08/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f35,plain,(
% 2.08/0.64    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.64    inference(rectify,[],[f34])).
% 2.08/0.64  fof(f34,plain,(
% 2.08/0.64    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.64    inference(nnf_transformation,[],[f3])).
% 2.08/0.64  fof(f3,axiom,(
% 2.08/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.08/0.64  fof(f67,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f41])).
% 2.08/0.64  fof(f41,plain,(
% 2.08/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 2.08/0.64  fof(f40,plain,(
% 2.08/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f39,plain,(
% 2.08/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.64    inference(rectify,[],[f38])).
% 2.08/0.64  fof(f38,plain,(
% 2.08/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.64    inference(nnf_transformation,[],[f31])).
% 2.08/0.64  fof(f31,plain,(
% 2.08/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f4])).
% 2.08/0.64  fof(f4,axiom,(
% 2.08/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.08/0.64  fof(f65,plain,(
% 2.08/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 2.08/0.64    inference(cnf_transformation,[],[f30])).
% 2.08/0.64  fof(f30,plain,(
% 2.08/0.64    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.08/0.64    inference(ennf_transformation,[],[f11])).
% 2.08/0.64  fof(f11,axiom,(
% 2.08/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 2.08/0.64  fof(f62,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f10])).
% 2.08/0.64  fof(f10,axiom,(
% 2.08/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.08/0.64  fof(f113,plain,(
% 2.08/0.64    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 2.08/0.64    inference(superposition,[],[f63,f56])).
% 2.08/0.64  fof(f56,plain,(
% 2.08/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.08/0.64    inference(cnf_transformation,[],[f27])).
% 2.08/0.64  fof(f27,plain,(
% 2.08/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.08/0.64    inference(rectify,[],[f5])).
% 2.08/0.64  fof(f5,axiom,(
% 2.08/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.08/0.64  fof(f1544,plain,(
% 2.08/0.64    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 2.08/0.64    inference(forward_demodulation,[],[f1464,f63])).
% 2.08/0.64  fof(f1464,plain,(
% 2.08/0.64    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) )),
% 2.08/0.64    inference(superposition,[],[f195,f73])).
% 2.08/0.64  fof(f195,plain,(
% 2.08/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 2.08/0.64    inference(superposition,[],[f64,f59])).
% 2.08/0.64  fof(f57,plain,(
% 2.08/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.08/0.64    inference(cnf_transformation,[],[f13])).
% 2.08/0.64  fof(f13,axiom,(
% 2.08/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.08/0.64  fof(f1755,plain,(
% 2.08/0.64    sK2 != k1_tarski(sK0)),
% 2.08/0.64    inference(subsumption_resolution,[],[f48,f1754])).
% 2.08/0.64  fof(f1754,plain,(
% 2.08/0.64    k1_xboole_0 = sK1),
% 2.08/0.64    inference(global_subsumption,[],[f47,f227,f234,f1745])).
% 2.08/0.65  fof(f234,plain,(
% 2.08/0.65    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.08/0.65    inference(trivial_inequality_removal,[],[f229])).
% 2.08/0.65  fof(f229,plain,(
% 2.08/0.65    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.08/0.65    inference(superposition,[],[f49,f227])).
% 2.08/0.65  fof(f49,plain,(
% 2.08/0.65    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.08/0.65    inference(cnf_transformation,[],[f33])).
% 2.08/0.65  fof(f227,plain,(
% 2.08/0.65    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.08/0.65    inference(resolution,[],[f69,f86])).
% 2.08/0.65  fof(f86,plain,(
% 2.08/0.65    r1_tarski(sK1,k1_tarski(sK0))),
% 2.08/0.65    inference(superposition,[],[f57,f46])).
% 2.08/0.65  fof(f47,plain,(
% 2.08/0.65    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.08/0.65    inference(cnf_transformation,[],[f33])).
% 2.08/0.65  fof(f48,plain,(
% 2.08/0.65    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.08/0.65    inference(cnf_transformation,[],[f33])).
% 2.08/0.65  fof(f1809,plain,(
% 2.08/0.65    k1_xboole_0 = k1_tarski(sK0)),
% 2.08/0.65    inference(forward_demodulation,[],[f1808,f1800])).
% 2.08/0.65  fof(f1808,plain,(
% 2.08/0.65    sK2 = k1_tarski(sK0)),
% 2.08/0.65    inference(forward_demodulation,[],[f1756,f183])).
% 2.08/0.65  fof(f1756,plain,(
% 2.08/0.65    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 2.08/0.65    inference(backward_demodulation,[],[f46,f1754])).
% 2.08/0.65  % SZS output end Proof for theBenchmark
% 2.08/0.65  % (20884)------------------------------
% 2.08/0.65  % (20884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (20884)Termination reason: Refutation
% 2.08/0.65  
% 2.08/0.65  % (20884)Memory used [KB]: 7547
% 2.08/0.65  % (20884)Time elapsed: 0.215 s
% 2.08/0.65  % (20884)------------------------------
% 2.08/0.65  % (20884)------------------------------
% 2.22/0.65  % (20876)Success in time 0.29 s
%------------------------------------------------------------------------------
