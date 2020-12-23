%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:36 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 557 expanded)
%              Number of leaves         :   22 ( 166 expanded)
%              Depth                    :   23
%              Number of atoms          :  270 (1910 expanded)
%              Number of equality atoms :   77 ( 538 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1714,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f166,f1541])).

fof(f1541,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = X5
      | ~ r2_hidden(X6,X5) ) ),
    inference(forward_demodulation,[],[f1535,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1535,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k1_xboole_0))
      | ~ r2_hidden(X6,X5) ) ),
    inference(backward_demodulation,[],[f407,f1525])).

fof(f1525,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f1505,f118])).

fof(f118,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f81,f79])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f50,f76,f76])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1505,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X9)),X9) ),
    inference(resolution,[],[f1497,f1260])).

fof(f1260,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3),X2)
      | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3) = X2 ) ),
    inference(backward_demodulation,[],[f184,f1236])).

fof(f1236,plain,(
    ! [X4,X3] : k3_xboole_0(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),X4) = X4 ),
    inference(resolution,[],[f1201,f121])).

fof(f121,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(superposition,[],[f80,f81])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X0) = X0 ) ),
    inference(superposition,[],[f1200,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1200,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f1191])).

fof(f1191,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))
      | k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f444,f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f312,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f312,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X1)
      | ~ r2_hidden(sK4(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X1)
      | ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f153,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f444,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,k3_xboole_0(X2,X0)),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X0) ) ),
    inference(factoring,[],[f138])).

fof(f138,plain,(
    ! [X17,X15,X18,X16] :
      ( r2_hidden(sK4(X15,X16,k3_xboole_0(X17,X18)),X18)
      | k3_xboole_0(X17,X18) = k3_xboole_0(X15,X16)
      | r2_hidden(sK4(X15,X16,k3_xboole_0(X17,X18)),X15) ) ),
    inference(resolution,[],[f70,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f184,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3),X2)
      | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3)) = X2 ) ),
    inference(resolution,[],[f83,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 ) ),
    inference(definition_unfolding,[],[f59,f53,f76])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f1497,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1473,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
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

fof(f1473,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f1449,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1449,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X7,k1_xboole_0) ) ),
    inference(resolution,[],[f1387,f1311])).

fof(f1311,plain,(
    ! [X30,X29] :
      ( r2_hidden(sK2(k1_xboole_0),X29)
      | ~ r2_hidden(X30,k1_xboole_0) ) ),
    inference(superposition,[],[f263,f1239])).

fof(f1239,plain,(
    ! [X8] : k1_xboole_0 = k3_xboole_0(X8,k1_xboole_0) ),
    inference(resolution,[],[f1201,f219])).

fof(f219,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f80,f118])).

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k3_xboole_0(X0,X1)),X0)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f95,f47])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | r2_hidden(sK2(k3_xboole_0(X0,X1)),X0) ) ),
    inference(resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1387,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,sK2(k1_xboole_0))
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(resolution,[],[f1311,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f407,plain,(
    ! [X6,X5] :
      ( k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X6))))
      | ~ r2_hidden(X6,X5) ) ),
    inference(resolution,[],[f159,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) ) ),
    inference(superposition,[],[f82,f58])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f54,f76,f76,f53])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f166,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f78,f81])).

fof(f78,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f44,f76,f77])).

fof(f44,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).

% (24093)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:18:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (24024)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (24025)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (24025)Refutation not found, incomplete strategy% (24025)------------------------------
% 0.21/0.54  % (24025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24033)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (24025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24025)Memory used [KB]: 1663
% 0.21/0.55  % (24025)Time elapsed: 0.112 s
% 0.21/0.55  % (24025)------------------------------
% 0.21/0.55  % (24025)------------------------------
% 1.43/0.55  % (24046)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.57  % (24030)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.57  % (24028)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.57  % (24029)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.57  % (24026)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.57  % (24027)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.57/0.57  % (24040)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.57/0.58  % (24041)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.59  % (24041)Refutation not found, incomplete strategy% (24041)------------------------------
% 1.57/0.59  % (24041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (24041)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (24041)Memory used [KB]: 1791
% 1.57/0.59  % (24041)Time elapsed: 0.121 s
% 1.57/0.59  % (24041)------------------------------
% 1.57/0.59  % (24041)------------------------------
% 1.57/0.59  % (24040)Refutation not found, incomplete strategy% (24040)------------------------------
% 1.57/0.59  % (24040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (24032)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.59  % (24040)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (24040)Memory used [KB]: 10618
% 1.57/0.59  % (24040)Time elapsed: 0.162 s
% 1.57/0.59  % (24040)------------------------------
% 1.57/0.59  % (24040)------------------------------
% 1.57/0.60  % (24047)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.60  % (24045)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.57/0.60  % (24051)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.60  % (24052)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.60  % (24052)Refutation not found, incomplete strategy% (24052)------------------------------
% 1.57/0.60  % (24052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (24052)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.60  
% 1.57/0.60  % (24052)Memory used [KB]: 10746
% 1.57/0.60  % (24052)Time elapsed: 0.183 s
% 1.57/0.60  % (24052)------------------------------
% 1.57/0.60  % (24052)------------------------------
% 1.57/0.60  % (24053)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.61  % (24034)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.57/0.61  % (24042)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.57/0.61  % (24053)Refutation not found, incomplete strategy% (24053)------------------------------
% 1.57/0.61  % (24053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (24034)Refutation not found, incomplete strategy% (24034)------------------------------
% 1.57/0.61  % (24034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (24038)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.61  % (24053)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (24053)Memory used [KB]: 1663
% 1.57/0.61  % (24053)Time elapsed: 0.184 s
% 1.57/0.61  % (24053)------------------------------
% 1.57/0.61  % (24053)------------------------------
% 1.57/0.61  % (24048)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.61  % (24044)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.57/0.61  % (24031)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.61  % (24043)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.61  % (24037)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.57/0.61  % (24039)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.57/0.61  % (24035)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.62  % (24049)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.62  % (24050)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.57/0.62  % (24036)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.62  % (24038)Refutation not found, incomplete strategy% (24038)------------------------------
% 1.57/0.62  % (24038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (24038)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (24038)Memory used [KB]: 1663
% 1.57/0.62  % (24038)Time elapsed: 0.194 s
% 1.57/0.62  % (24038)------------------------------
% 1.57/0.62  % (24038)------------------------------
% 1.57/0.62  % (24036)Refutation not found, incomplete strategy% (24036)------------------------------
% 1.57/0.62  % (24036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (24036)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (24036)Memory used [KB]: 10618
% 1.57/0.62  % (24036)Time elapsed: 0.193 s
% 1.57/0.62  % (24036)------------------------------
% 1.57/0.62  % (24036)------------------------------
% 1.57/0.63  % (24034)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.63  
% 1.57/0.63  % (24034)Memory used [KB]: 10746
% 1.57/0.63  % (24034)Time elapsed: 0.185 s
% 1.57/0.63  % (24034)------------------------------
% 1.57/0.63  % (24034)------------------------------
% 2.33/0.69  % (24091)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.33/0.71  % (24024)Refutation not found, incomplete strategy% (24024)------------------------------
% 2.33/0.71  % (24024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.71  % (24024)Termination reason: Refutation not found, incomplete strategy
% 2.33/0.71  
% 2.33/0.71  % (24024)Memory used [KB]: 1791
% 2.33/0.71  % (24024)Time elapsed: 0.282 s
% 2.33/0.71  % (24024)------------------------------
% 2.33/0.71  % (24024)------------------------------
% 2.33/0.72  % (24046)Refutation found. Thanks to Tanya!
% 2.33/0.72  % SZS status Theorem for theBenchmark
% 2.33/0.72  % SZS output start Proof for theBenchmark
% 2.33/0.72  fof(f1714,plain,(
% 2.33/0.72    $false),
% 2.33/0.72    inference(unit_resulting_resolution,[],[f43,f166,f1541])).
% 2.33/0.72  fof(f1541,plain,(
% 2.33/0.72    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = X5 | ~r2_hidden(X6,X5)) )),
% 2.33/0.72    inference(forward_demodulation,[],[f1535,f79])).
% 2.33/0.72  fof(f79,plain,(
% 2.33/0.72    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 2.33/0.72    inference(definition_unfolding,[],[f45,f76])).
% 2.33/0.72  fof(f76,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.33/0.72    inference(definition_unfolding,[],[f51,f75])).
% 2.33/0.72  fof(f75,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.33/0.72    inference(definition_unfolding,[],[f52,f74])).
% 2.33/0.72  fof(f74,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.33/0.72    inference(definition_unfolding,[],[f66,f73])).
% 2.33/0.72  fof(f73,plain,(
% 2.33/0.72    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f16])).
% 2.33/0.72  fof(f16,axiom,(
% 2.33/0.72    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.33/0.72  fof(f66,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f15])).
% 2.33/0.72  fof(f15,axiom,(
% 2.33/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.33/0.72  fof(f52,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f14])).
% 2.33/0.72  fof(f14,axiom,(
% 2.33/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.33/0.72  fof(f51,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.33/0.72    inference(cnf_transformation,[],[f18])).
% 2.33/0.72  fof(f18,axiom,(
% 2.33/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.33/0.72  fof(f45,plain,(
% 2.33/0.72    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.33/0.72    inference(cnf_transformation,[],[f8])).
% 2.33/0.72  fof(f8,axiom,(
% 2.33/0.72    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.33/0.72  fof(f1535,plain,(
% 2.33/0.72    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k1_xboole_0)) | ~r2_hidden(X6,X5)) )),
% 2.33/0.72    inference(backward_demodulation,[],[f407,f1525])).
% 2.33/0.72  fof(f1525,plain,(
% 2.33/0.72    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,X9)) )),
% 2.33/0.72    inference(forward_demodulation,[],[f1505,f118])).
% 2.33/0.72  fof(f118,plain,(
% 2.33/0.72    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 2.33/0.72    inference(superposition,[],[f81,f79])).
% 2.33/0.72  fof(f81,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 2.33/0.72    inference(definition_unfolding,[],[f50,f76,f76])).
% 2.33/0.72  fof(f50,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f2])).
% 2.33/0.72  fof(f2,axiom,(
% 2.33/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.33/0.72  fof(f1505,plain,(
% 2.33/0.72    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X9)),X9)) )),
% 2.33/0.72    inference(resolution,[],[f1497,f1260])).
% 2.33/0.72  fof(f1260,plain,(
% 2.33/0.72    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3),X2) | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3) = X2) )),
% 2.33/0.72    inference(backward_demodulation,[],[f184,f1236])).
% 2.33/0.72  fof(f1236,plain,(
% 2.33/0.72    ( ! [X4,X3] : (k3_xboole_0(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),X4) = X4) )),
% 2.33/0.72    inference(resolution,[],[f1201,f121])).
% 2.33/0.72  fof(f121,plain,(
% 2.33/0.72    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) )),
% 2.33/0.72    inference(superposition,[],[f80,f81])).
% 2.33/0.72  fof(f80,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.33/0.72    inference(definition_unfolding,[],[f49,f76])).
% 2.33/0.72  fof(f49,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.33/0.72    inference(cnf_transformation,[],[f11])).
% 2.33/0.72  fof(f11,axiom,(
% 2.33/0.72    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.33/0.72  fof(f1201,plain,(
% 2.33/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0) )),
% 2.33/0.72    inference(superposition,[],[f1200,f58])).
% 2.33/0.72  fof(f58,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f24])).
% 2.33/0.72  fof(f24,plain,(
% 2.33/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.33/0.72    inference(ennf_transformation,[],[f9])).
% 2.33/0.72  fof(f9,axiom,(
% 2.33/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.33/0.72  fof(f1200,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.33/0.72    inference(duplicate_literal_removal,[],[f1191])).
% 2.33/0.72  fof(f1191,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) | k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.33/0.72    inference(resolution,[],[f444,f313])).
% 2.33/0.72  fof(f313,plain,(
% 2.33/0.72    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 2.33/0.72    inference(subsumption_resolution,[],[f312,f153])).
% 2.33/0.72  fof(f153,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 2.33/0.72    inference(factoring,[],[f71])).
% 2.33/0.72  fof(f71,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 2.33/0.72    inference(cnf_transformation,[],[f42])).
% 2.33/0.72  fof(f42,plain,(
% 2.33/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.33/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 2.33/0.72  fof(f41,plain,(
% 2.33/0.72    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.33/0.72    introduced(choice_axiom,[])).
% 2.33/0.72  fof(f40,plain,(
% 2.33/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.33/0.72    inference(rectify,[],[f39])).
% 2.33/0.72  fof(f39,plain,(
% 2.33/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.33/0.72    inference(flattening,[],[f38])).
% 2.33/0.72  fof(f38,plain,(
% 2.33/0.72    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.33/0.72    inference(nnf_transformation,[],[f4])).
% 2.33/0.72  fof(f4,axiom,(
% 2.33/0.72    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.33/0.72  fof(f312,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK4(X0,X1,X1),X1) | ~r2_hidden(sK4(X0,X1,X1),X0)) )),
% 2.33/0.72    inference(duplicate_literal_removal,[],[f306])).
% 2.33/0.72  fof(f306,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK4(X0,X1,X1),X1) | ~r2_hidden(sK4(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 2.33/0.72    inference(resolution,[],[f153,f72])).
% 2.33/0.72  fof(f72,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.33/0.72    inference(cnf_transformation,[],[f42])).
% 2.33/0.72  fof(f444,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,k3_xboole_0(X2,X0)),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X0)) )),
% 2.33/0.72    inference(factoring,[],[f138])).
% 2.33/0.72  fof(f138,plain,(
% 2.33/0.72    ( ! [X17,X15,X18,X16] : (r2_hidden(sK4(X15,X16,k3_xboole_0(X17,X18)),X18) | k3_xboole_0(X17,X18) = k3_xboole_0(X15,X16) | r2_hidden(sK4(X15,X16,k3_xboole_0(X17,X18)),X15)) )),
% 2.33/0.72    inference(resolution,[],[f70,f89])).
% 2.33/0.72  fof(f89,plain,(
% 2.33/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 2.33/0.72    inference(equality_resolution,[],[f68])).
% 2.33/0.72  fof(f68,plain,(
% 2.33/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.33/0.72    inference(cnf_transformation,[],[f42])).
% 2.33/0.72  fof(f70,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.33/0.72    inference(cnf_transformation,[],[f42])).
% 2.33/0.72  fof(f184,plain,(
% 2.33/0.72    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3),X2) | k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3)) = X2) )),
% 2.33/0.72    inference(resolution,[],[f83,f55])).
% 2.33/0.72  fof(f55,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f34])).
% 2.33/0.72  fof(f34,plain,(
% 2.33/0.72    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.33/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f33])).
% 2.33/0.72  fof(f33,plain,(
% 2.33/0.72    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.33/0.72    introduced(choice_axiom,[])).
% 2.33/0.72  fof(f23,plain,(
% 2.33/0.72    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.33/0.72    inference(ennf_transformation,[],[f21])).
% 2.33/0.72  fof(f21,plain,(
% 2.33/0.72    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.33/0.72    inference(rectify,[],[f5])).
% 2.33/0.72  fof(f5,axiom,(
% 2.33/0.72    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.33/0.72  fof(f83,plain,(
% 2.33/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0) )),
% 2.33/0.72    inference(definition_unfolding,[],[f59,f53,f76])).
% 2.33/0.72  fof(f53,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.33/0.72    inference(cnf_transformation,[],[f7])).
% 2.33/0.72  fof(f7,axiom,(
% 2.33/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.33/0.72  fof(f59,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f25])).
% 2.33/0.72  fof(f25,plain,(
% 2.33/0.72    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.33/0.72    inference(ennf_transformation,[],[f12])).
% 2.33/0.72  fof(f12,axiom,(
% 2.33/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 2.33/0.72  fof(f1497,plain,(
% 2.33/0.72    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 2.33/0.72    inference(subsumption_resolution,[],[f1473,f47])).
% 2.33/0.72  fof(f47,plain,(
% 2.33/0.72    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f32])).
% 2.33/0.72  fof(f32,plain,(
% 2.33/0.72    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 2.33/0.72  fof(f31,plain,(
% 2.33/0.72    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.33/0.72    introduced(choice_axiom,[])).
% 2.33/0.72  fof(f30,plain,(
% 2.33/0.72    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/0.72    inference(rectify,[],[f29])).
% 2.33/0.72  fof(f29,plain,(
% 2.33/0.72    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.33/0.72    inference(nnf_transformation,[],[f3])).
% 2.33/0.72  fof(f3,axiom,(
% 2.33/0.72    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.33/0.72  fof(f1473,plain,(
% 2.33/0.72    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | v1_xboole_0(k1_xboole_0)) )),
% 2.33/0.72    inference(resolution,[],[f1449,f48])).
% 2.33/0.72  fof(f48,plain,(
% 2.33/0.72    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f32])).
% 2.33/0.72  fof(f1449,plain,(
% 2.33/0.72    ( ! [X6,X7] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X7,k1_xboole_0)) )),
% 2.33/0.72    inference(resolution,[],[f1387,f1311])).
% 2.33/0.72  fof(f1311,plain,(
% 2.33/0.72    ( ! [X30,X29] : (r2_hidden(sK2(k1_xboole_0),X29) | ~r2_hidden(X30,k1_xboole_0)) )),
% 2.33/0.72    inference(superposition,[],[f263,f1239])).
% 2.33/0.72  fof(f1239,plain,(
% 2.33/0.72    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(X8,k1_xboole_0)) )),
% 2.33/0.72    inference(resolution,[],[f1201,f219])).
% 2.33/0.72  fof(f219,plain,(
% 2.33/0.72    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.33/0.72    inference(superposition,[],[f80,f118])).
% 2.33/0.72  fof(f263,plain,(
% 2.33/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK2(k3_xboole_0(X0,X1)),X0) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.33/0.72    inference(resolution,[],[f95,f47])).
% 2.33/0.72  fof(f95,plain,(
% 2.33/0.72    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | r2_hidden(sK2(k3_xboole_0(X0,X1)),X0)) )),
% 2.33/0.72    inference(resolution,[],[f90,f48])).
% 2.33/0.72  fof(f90,plain,(
% 2.33/0.72    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.33/0.72    inference(equality_resolution,[],[f67])).
% 2.33/0.72  fof(f67,plain,(
% 2.33/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.33/0.72    inference(cnf_transformation,[],[f42])).
% 2.33/0.72  fof(f1387,plain,(
% 2.33/0.72    ( ! [X6,X7] : (~r2_hidden(X7,sK2(k1_xboole_0)) | ~r2_hidden(X6,k1_xboole_0)) )),
% 2.33/0.72    inference(resolution,[],[f1311,f60])).
% 2.33/0.72  fof(f60,plain,(
% 2.33/0.72    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f26])).
% 2.33/0.72  fof(f26,plain,(
% 2.33/0.72    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.33/0.72    inference(ennf_transformation,[],[f1])).
% 2.33/0.72  fof(f1,axiom,(
% 2.33/0.72    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 2.33/0.72  fof(f407,plain,(
% 2.33/0.72    ( ! [X6,X5] : (k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X6,X6,X6,X6,X6))) = k3_tarski(k3_enumset1(X5,X5,X5,X5,k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X6,X6,X6,X6,X6)))) | ~r2_hidden(X6,X5)) )),
% 2.33/0.72    inference(resolution,[],[f159,f84])).
% 2.33/0.72  fof(f84,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.33/0.72    inference(definition_unfolding,[],[f65,f77])).
% 2.33/0.72  fof(f77,plain,(
% 2.33/0.72    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.33/0.72    inference(definition_unfolding,[],[f46,f75])).
% 2.33/0.72  fof(f46,plain,(
% 2.33/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f13])).
% 2.33/0.72  fof(f13,axiom,(
% 2.33/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.33/0.72  fof(f65,plain,(
% 2.33/0.72    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.33/0.72    inference(cnf_transformation,[],[f37])).
% 2.33/0.72  fof(f37,plain,(
% 2.33/0.72    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.33/0.72    inference(nnf_transformation,[],[f17])).
% 2.33/0.72  fof(f17,axiom,(
% 2.33/0.72    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.33/0.72  fof(f159,plain,(
% 2.33/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))) )),
% 2.33/0.72    inference(superposition,[],[f82,f58])).
% 2.33/0.72  fof(f82,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.33/0.72    inference(definition_unfolding,[],[f54,f76,f76,f53])).
% 2.33/0.72  fof(f54,plain,(
% 2.33/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.33/0.72    inference(cnf_transformation,[],[f10])).
% 2.33/0.72  fof(f10,axiom,(
% 2.33/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.33/0.72  fof(f166,plain,(
% 2.33/0.72    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.33/0.72    inference(superposition,[],[f78,f81])).
% 2.33/0.72  fof(f78,plain,(
% 2.33/0.72    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 2.33/0.72    inference(definition_unfolding,[],[f44,f76,f77])).
% 2.33/0.72  fof(f44,plain,(
% 2.33/0.72    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.33/0.72    inference(cnf_transformation,[],[f28])).
% 2.33/0.72  fof(f28,plain,(
% 2.33/0.72    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 2.33/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).
% 2.33/0.72  % (24093)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.33/0.72  fof(f27,plain,(
% 2.33/0.72    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 2.33/0.72    introduced(choice_axiom,[])).
% 2.33/0.72  fof(f22,plain,(
% 2.33/0.72    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 2.33/0.72    inference(ennf_transformation,[],[f20])).
% 2.33/0.72  fof(f20,negated_conjecture,(
% 2.33/0.72    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.33/0.72    inference(negated_conjecture,[],[f19])).
% 2.33/0.72  fof(f19,conjecture,(
% 2.33/0.72    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.33/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 2.33/0.72  fof(f43,plain,(
% 2.33/0.72    r2_hidden(sK0,sK1)),
% 2.33/0.72    inference(cnf_transformation,[],[f28])).
% 2.33/0.72  % SZS output end Proof for theBenchmark
% 2.33/0.72  % (24046)------------------------------
% 2.33/0.72  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.72  % (24046)Termination reason: Refutation
% 2.33/0.72  
% 2.33/0.72  % (24046)Memory used [KB]: 7547
% 2.33/0.72  % (24046)Time elapsed: 0.281 s
% 2.33/0.72  % (24046)------------------------------
% 2.33/0.72  % (24046)------------------------------
% 2.33/0.72  % (24023)Success in time 0.353 s
%------------------------------------------------------------------------------
