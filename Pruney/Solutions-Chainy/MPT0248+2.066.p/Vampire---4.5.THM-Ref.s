%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:58 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  141 (4348 expanded)
%              Number of leaves         :   23 (1219 expanded)
%              Depth                    :   28
%              Number of atoms          :  366 (11905 expanded)
%              Number of equality atoms :  175 (5982 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1834,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1833,f1489])).

fof(f1489,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f60,f1487])).

fof(f1487,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(global_subsumption,[],[f59,f884,f1468])).

fof(f1468,plain,
    ( sK2 = k1_tarski(sK0)
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f966,f57])).

fof(f57,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f39])).

fof(f39,plain,
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

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f966,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,X0) = X0
      | sK1 = k1_tarski(sK0) ) ),
    inference(resolution,[],[f839,f233])).

fof(f233,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f226,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f226,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f81,f110])).

fof(f110,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f839,plain,(
    ! [X4] :
      ( r2_hidden(sK0,sK1)
      | k2_xboole_0(sK1,X4) = X4 ) ),
    inference(forward_demodulation,[],[f834,f523])).

fof(f523,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f352,f507])).

fof(f507,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f486,f481])).

fof(f481,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f459,f354])).

fof(f354,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f353,f66])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f353,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f343,f65])).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f343,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f72,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f459,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f94,f61])).

fof(f94,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f486,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f481,f69])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f352,plain,(
    k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f72,f135])).

fof(f135,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f78,f110])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f834,plain,(
    ! [X4] :
      ( r2_hidden(sK0,sK1)
      | k2_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),X4) = X4 ) ),
    inference(resolution,[],[f828,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2 ) ),
    inference(resolution,[],[f140,f78])).

fof(f140,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k3_xboole_0(X2,X3),X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f83,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f828,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f827,f160])).

fof(f160,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X3,X4)
      | k1_xboole_0 != X3 ) ),
    inference(resolution,[],[f157,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f154,f66])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f86,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f74,f66])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f827,plain,
    ( r2_hidden(sK0,sK1)
    | r1_xboole_0(sK1,k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f765])).

fof(f765,plain,
    ( sK0 = sK4(sK1,k1_tarski(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f597,f224])).

fof(f224,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k1_xboole_0)
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f81,f141])).

fof(f141,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(resolution,[],[f83,f120])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f119,f99])).

fof(f99,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f597,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK0 = sK4(sK1,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f531,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k1_tarski(X1))
      | sK4(X0,k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f76,f104])).

fof(f104,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f531,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f140,f523])).

fof(f884,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f842,f233])).

fof(f842,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f838,f523])).

fof(f838,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f828,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f59,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f1833,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1817,f224])).

fof(f1817,plain,(
    ! [X3] : r1_tarski(sK2,X3) ),
    inference(subsumption_resolution,[],[f1605,f1815])).

fof(f1815,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1813,f1608])).

fof(f1608,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1114,f1575])).

fof(f1575,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f158,f1487])).

fof(f158,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(resolution,[],[f157,f103])).

fof(f103,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1114,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1110,f935])).

fof(f935,plain,(
    ! [X5] :
      ( r1_tarski(sK1,X5)
      | ~ r2_hidden(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f908,f162])).

fof(f162,plain,(
    ! [X8,X7] :
      ( r1_tarski(X7,X8)
      | k1_xboole_0 != X7 ) ),
    inference(resolution,[],[f157,f83])).

fof(f908,plain,(
    ! [X5] :
      ( r1_tarski(sK1,X5)
      | ~ r2_hidden(sK0,X5)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f92,f884])).

fof(f1110,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f106,f884,f1107])).

fof(f1107,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f222,f933])).

fof(f933,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f897,f508])).

fof(f508,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f486,f486])).

fof(f897,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f351,f884])).

fof(f351,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f72,f57])).

fof(f222,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k3_xboole_0(X5,X6))
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f106,plain,
    ( sK1 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f105])).

fof(f105,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1813,plain,
    ( r2_hidden(sK0,sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f76,f1812])).

fof(f1812,plain,(
    sK0 = sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1811,f1489])).

fof(f1811,plain,
    ( sK0 = sK4(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1723,f224])).

fof(f1723,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | sK0 = sK4(sK1,sK2) ) ),
    inference(resolution,[],[f1605,f937])).

fof(f937,plain,(
    ! [X8] :
      ( r1_xboole_0(sK1,X8)
      | sK0 = sK4(sK1,X8) ) ),
    inference(subsumption_resolution,[],[f913,f160])).

fof(f913,plain,(
    ! [X8] :
      ( r1_xboole_0(sK1,X8)
      | sK0 = sK4(sK1,X8)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f121,f884])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f75,f104])).

fof(f1605,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK1,sK2)
      | r1_tarski(sK2,X3) ) ),
    inference(subsumption_resolution,[],[f1106,f1575])).

fof(f1106,plain,(
    ! [X3] :
      ( r1_tarski(sK2,X3)
      | ~ r1_xboole_0(sK1,sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f140,f933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (32601)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (32611)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (32623)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32624)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (32615)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (32627)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (32619)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (32607)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (32610)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (32605)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32608)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32612)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (32606)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32620)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.53  % (32613)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (32604)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.54  % (32628)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (32603)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (32629)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (32630)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.55  % (32621)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.55  % (32626)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.55  % (32622)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.56  % (32614)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.56  % (32618)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.57  % (32602)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.58  % (32625)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.58  % (32616)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.59  % (32617)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.59  % (32609)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.62  % (32608)Refutation found. Thanks to Tanya!
% 1.49/0.62  % SZS status Theorem for theBenchmark
% 2.03/0.63  % SZS output start Proof for theBenchmark
% 2.03/0.63  fof(f1834,plain,(
% 2.03/0.63    $false),
% 2.03/0.63    inference(subsumption_resolution,[],[f1833,f1489])).
% 2.03/0.63  fof(f1489,plain,(
% 2.03/0.63    k1_xboole_0 != sK2),
% 2.03/0.63    inference(subsumption_resolution,[],[f60,f1487])).
% 2.03/0.63  fof(f1487,plain,(
% 2.03/0.63    sK1 = k1_tarski(sK0)),
% 2.03/0.63    inference(global_subsumption,[],[f59,f884,f1468])).
% 2.03/0.63  fof(f1468,plain,(
% 2.03/0.63    sK2 = k1_tarski(sK0) | sK1 = k1_tarski(sK0)),
% 2.03/0.63    inference(superposition,[],[f966,f57])).
% 2.03/0.63  fof(f57,plain,(
% 2.03/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.03/0.63    inference(cnf_transformation,[],[f40])).
% 2.03/0.63  fof(f40,plain,(
% 2.03/0.63    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f39])).
% 2.03/0.63  fof(f39,plain,(
% 2.03/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f33,plain,(
% 2.03/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.03/0.63    inference(ennf_transformation,[],[f28])).
% 2.03/0.63  fof(f28,negated_conjecture,(
% 2.03/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.03/0.63    inference(negated_conjecture,[],[f27])).
% 2.03/0.63  fof(f27,conjecture,(
% 2.03/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.03/0.63  fof(f966,plain,(
% 2.03/0.63    ( ! [X0] : (k2_xboole_0(sK1,X0) = X0 | sK1 = k1_tarski(sK0)) )),
% 2.03/0.63    inference(resolution,[],[f839,f233])).
% 2.03/0.63  fof(f233,plain,(
% 2.03/0.63    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 2.03/0.63    inference(resolution,[],[f226,f92])).
% 2.03/0.63  fof(f92,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f56])).
% 2.03/0.63  fof(f56,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.03/0.63    inference(nnf_transformation,[],[f25])).
% 2.03/0.63  fof(f25,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.03/0.63  fof(f226,plain,(
% 2.03/0.63    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 2.03/0.63    inference(resolution,[],[f81,f110])).
% 2.03/0.63  fof(f110,plain,(
% 2.03/0.63    r1_tarski(sK1,k1_tarski(sK0))),
% 2.03/0.63    inference(superposition,[],[f67,f57])).
% 2.03/0.63  fof(f67,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f13])).
% 2.03/0.63  fof(f13,axiom,(
% 2.03/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.03/0.63  fof(f81,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f46])).
% 2.03/0.63  fof(f46,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(flattening,[],[f45])).
% 2.03/0.63  fof(f45,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(nnf_transformation,[],[f9])).
% 2.03/0.63  fof(f9,axiom,(
% 2.03/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.63  fof(f839,plain,(
% 2.03/0.63    ( ! [X4] : (r2_hidden(sK0,sK1) | k2_xboole_0(sK1,X4) = X4) )),
% 2.03/0.63    inference(forward_demodulation,[],[f834,f523])).
% 2.03/0.63  fof(f523,plain,(
% 2.03/0.63    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.03/0.63    inference(backward_demodulation,[],[f352,f507])).
% 2.03/0.63  fof(f507,plain,(
% 2.03/0.63    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.03/0.63    inference(superposition,[],[f486,f481])).
% 2.03/0.63  fof(f481,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.03/0.63    inference(forward_demodulation,[],[f459,f354])).
% 2.03/0.63  fof(f354,plain,(
% 2.03/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.03/0.63    inference(forward_demodulation,[],[f353,f66])).
% 2.03/0.63  fof(f66,plain,(
% 2.03/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.03/0.63    inference(cnf_transformation,[],[f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.03/0.63    inference(rectify,[],[f6])).
% 2.03/0.63  fof(f6,axiom,(
% 2.03/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.03/0.63  fof(f353,plain,(
% 2.03/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.03/0.63    inference(forward_demodulation,[],[f343,f65])).
% 2.03/0.63  fof(f65,plain,(
% 2.03/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.03/0.63    inference(cnf_transformation,[],[f29])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.03/0.63    inference(rectify,[],[f5])).
% 2.03/0.63  fof(f5,axiom,(
% 2.03/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.03/0.63  fof(f343,plain,(
% 2.03/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 2.03/0.63    inference(superposition,[],[f72,f61])).
% 2.03/0.63  fof(f61,plain,(
% 2.03/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f15])).
% 2.03/0.63  fof(f15,axiom,(
% 2.03/0.63    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.03/0.63  fof(f72,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f16,axiom,(
% 2.03/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.03/0.63  fof(f459,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.03/0.63    inference(superposition,[],[f94,f61])).
% 2.03/0.63  fof(f94,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f14])).
% 2.03/0.63  fof(f14,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.03/0.63  fof(f486,plain,(
% 2.03/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.03/0.63    inference(superposition,[],[f481,f69])).
% 2.03/0.63  fof(f69,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f1])).
% 2.03/0.63  fof(f1,axiom,(
% 2.03/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.03/0.63  fof(f352,plain,(
% 2.03/0.63    k3_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.03/0.63    inference(superposition,[],[f72,f135])).
% 2.03/0.63  fof(f135,plain,(
% 2.03/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))),
% 2.03/0.63    inference(resolution,[],[f78,f110])).
% 2.03/0.63  fof(f78,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f37])).
% 2.03/0.63  fof(f37,plain,(
% 2.03/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.03/0.63    inference(ennf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.03/0.63  fof(f834,plain,(
% 2.03/0.63    ( ! [X4] : (r2_hidden(sK0,sK1) | k2_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),X4) = X4) )),
% 2.03/0.63    inference(resolution,[],[f828,f195])).
% 2.03/0.63  fof(f195,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2) )),
% 2.03/0.63    inference(resolution,[],[f140,f78])).
% 2.03/0.63  fof(f140,plain,(
% 2.03/0.63    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X4) | ~r1_xboole_0(X2,X3)) )),
% 2.03/0.63    inference(resolution,[],[f83,f74])).
% 2.03/0.63  fof(f74,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f42])).
% 2.03/0.63  fof(f42,plain,(
% 2.03/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f41])).
% 2.03/0.63  fof(f41,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f35,plain,(
% 2.03/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f31])).
% 2.03/0.63  fof(f31,plain,(
% 2.03/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(rectify,[],[f8])).
% 2.03/0.63  fof(f8,axiom,(
% 2.03/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.03/0.63  fof(f83,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f50])).
% 2.03/0.63  fof(f50,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 2.03/0.63  fof(f49,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f48,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(rectify,[],[f47])).
% 2.03/0.63  fof(f47,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.03/0.63    inference(nnf_transformation,[],[f38])).
% 2.03/0.63  fof(f38,plain,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f3])).
% 2.03/0.63  fof(f3,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.03/0.63  fof(f828,plain,(
% 2.03/0.63    r1_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK0,sK1)),
% 2.03/0.63    inference(subsumption_resolution,[],[f827,f160])).
% 2.03/0.63  fof(f160,plain,(
% 2.03/0.63    ( ! [X4,X3] : (r1_xboole_0(X3,X4) | k1_xboole_0 != X3) )),
% 2.03/0.63    inference(resolution,[],[f157,f75])).
% 2.03/0.63  fof(f75,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f44])).
% 2.03/0.63  fof(f44,plain,(
% 2.03/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f43])).
% 2.03/0.63  fof(f43,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f36,plain,(
% 2.03/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(ennf_transformation,[],[f32])).
% 2.03/0.63  fof(f32,plain,(
% 2.03/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(rectify,[],[f7])).
% 2.03/0.63  fof(f7,axiom,(
% 2.03/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.03/0.63  fof(f157,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 2.03/0.63    inference(forward_demodulation,[],[f154,f66])).
% 2.03/0.63  fof(f154,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 2.03/0.63    inference(resolution,[],[f86,f119])).
% 2.03/0.63  fof(f119,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 2.03/0.63    inference(superposition,[],[f74,f66])).
% 2.03/0.63  fof(f86,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.03/0.63    inference(cnf_transformation,[],[f51])).
% 2.03/0.63  fof(f51,plain,(
% 2.03/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.03/0.63    inference(nnf_transformation,[],[f4])).
% 2.03/0.63  fof(f4,axiom,(
% 2.03/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.03/0.63  fof(f827,plain,(
% 2.03/0.63    r2_hidden(sK0,sK1) | r1_xboole_0(sK1,k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(superposition,[],[f75,f765])).
% 2.03/0.63  fof(f765,plain,(
% 2.03/0.63    sK0 = sK4(sK1,k1_tarski(sK0)) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(resolution,[],[f597,f224])).
% 2.03/0.63  fof(f224,plain,(
% 2.03/0.63    ( ! [X10] : (~r1_tarski(X10,k1_xboole_0) | k1_xboole_0 = X10) )),
% 2.03/0.63    inference(resolution,[],[f81,f141])).
% 2.03/0.63  fof(f141,plain,(
% 2.03/0.63    ( ! [X5] : (r1_tarski(k1_xboole_0,X5)) )),
% 2.03/0.63    inference(resolution,[],[f83,f120])).
% 2.03/0.63  fof(f120,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.03/0.63    inference(resolution,[],[f119,f99])).
% 2.03/0.63  fof(f99,plain,(
% 2.03/0.63    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.03/0.63    inference(equality_resolution,[],[f63])).
% 2.03/0.63  fof(f63,plain,(
% 2.03/0.63    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f34])).
% 2.03/0.63  fof(f34,plain,(
% 2.03/0.63    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f12])).
% 2.03/0.63  fof(f12,axiom,(
% 2.03/0.63    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.03/0.63  fof(f597,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(sK1,X0) | sK0 = sK4(sK1,k1_tarski(sK0))) )),
% 2.03/0.63    inference(resolution,[],[f531,f126])).
% 2.03/0.63  fof(f126,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,k1_tarski(X1)) | sK4(X0,k1_tarski(X1)) = X1) )),
% 2.03/0.63    inference(resolution,[],[f76,f104])).
% 2.03/0.63  fof(f104,plain,(
% 2.03/0.63    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.03/0.63    inference(equality_resolution,[],[f87])).
% 2.03/0.63  fof(f87,plain,(
% 2.03/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f55])).
% 2.03/0.63  fof(f55,plain,(
% 2.03/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).
% 2.03/0.63  fof(f54,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f53,plain,(
% 2.03/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.03/0.63    inference(rectify,[],[f52])).
% 2.03/0.63  fof(f52,plain,(
% 2.03/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.03/0.63    inference(nnf_transformation,[],[f17])).
% 2.03/0.63  fof(f17,axiom,(
% 2.03/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.03/0.63  fof(f76,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f44])).
% 2.03/0.63  fof(f531,plain,(
% 2.03/0.63    ( ! [X0] : (~r1_xboole_0(sK1,k1_tarski(sK0)) | r1_tarski(sK1,X0)) )),
% 2.03/0.63    inference(superposition,[],[f140,f523])).
% 2.03/0.63  fof(f884,plain,(
% 2.03/0.63    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(resolution,[],[f842,f233])).
% 2.03/0.63  fof(f842,plain,(
% 2.03/0.63    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(forward_demodulation,[],[f838,f523])).
% 2.03/0.63  fof(f838,plain,(
% 2.03/0.63    r2_hidden(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.03/0.63    inference(resolution,[],[f828,f85])).
% 2.03/0.63  fof(f85,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.03/0.63    inference(cnf_transformation,[],[f51])).
% 2.03/0.63  fof(f59,plain,(
% 2.03/0.63    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.03/0.63    inference(cnf_transformation,[],[f40])).
% 2.03/0.63  fof(f60,plain,(
% 2.03/0.63    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.03/0.63    inference(cnf_transformation,[],[f40])).
% 2.03/0.63  fof(f1833,plain,(
% 2.03/0.63    k1_xboole_0 = sK2),
% 2.03/0.63    inference(resolution,[],[f1817,f224])).
% 2.03/0.63  fof(f1817,plain,(
% 2.03/0.63    ( ! [X3] : (r1_tarski(sK2,X3)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f1605,f1815])).
% 2.03/0.63  fof(f1815,plain,(
% 2.03/0.63    r1_xboole_0(sK1,sK2)),
% 2.03/0.63    inference(subsumption_resolution,[],[f1813,f1608])).
% 2.03/0.63  fof(f1608,plain,(
% 2.03/0.63    ~r2_hidden(sK0,sK2)),
% 2.03/0.63    inference(subsumption_resolution,[],[f1114,f1575])).
% 2.03/0.63  fof(f1575,plain,(
% 2.03/0.63    k1_xboole_0 != sK1),
% 2.03/0.63    inference(superposition,[],[f158,f1487])).
% 2.03/0.63  fof(f158,plain,(
% 2.03/0.63    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 2.03/0.63    inference(resolution,[],[f157,f103])).
% 2.03/0.63  fof(f103,plain,(
% 2.03/0.63    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.03/0.63    inference(equality_resolution,[],[f102])).
% 2.03/0.63  fof(f102,plain,(
% 2.03/0.63    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.03/0.63    inference(equality_resolution,[],[f88])).
% 2.03/0.63  fof(f88,plain,(
% 2.03/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f55])).
% 2.03/0.63  fof(f1114,plain,(
% 2.03/0.63    ~r2_hidden(sK0,sK2) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(resolution,[],[f1110,f935])).
% 2.03/0.63  fof(f935,plain,(
% 2.03/0.63    ( ! [X5] : (r1_tarski(sK1,X5) | ~r2_hidden(sK0,X5)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f908,f162])).
% 2.03/0.63  fof(f162,plain,(
% 2.03/0.63    ( ! [X8,X7] : (r1_tarski(X7,X8) | k1_xboole_0 != X7) )),
% 2.03/0.63    inference(resolution,[],[f157,f83])).
% 2.03/0.63  fof(f908,plain,(
% 2.03/0.63    ( ! [X5] : (r1_tarski(sK1,X5) | ~r2_hidden(sK0,X5) | k1_xboole_0 = sK1) )),
% 2.03/0.63    inference(superposition,[],[f92,f884])).
% 2.03/0.63  fof(f1110,plain,(
% 2.03/0.63    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(global_subsumption,[],[f106,f884,f1107])).
% 2.03/0.63  fof(f1107,plain,(
% 2.03/0.63    ~r1_tarski(sK1,sK2) | sK1 = sK2 | k1_xboole_0 = sK1),
% 2.03/0.63    inference(superposition,[],[f222,f933])).
% 2.03/0.63  fof(f933,plain,(
% 2.03/0.63    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(forward_demodulation,[],[f897,f508])).
% 2.03/0.63  fof(f508,plain,(
% 2.03/0.63    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 2.03/0.63    inference(superposition,[],[f486,f486])).
% 2.03/0.63  fof(f897,plain,(
% 2.03/0.63    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | k1_xboole_0 = sK1),
% 2.03/0.63    inference(superposition,[],[f351,f884])).
% 2.03/0.63  fof(f351,plain,(
% 2.03/0.63    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 2.03/0.63    inference(superposition,[],[f72,f57])).
% 2.03/0.63  fof(f222,plain,(
% 2.03/0.63    ( ! [X6,X5] : (~r1_tarski(X5,k3_xboole_0(X5,X6)) | k3_xboole_0(X5,X6) = X5) )),
% 2.03/0.63    inference(resolution,[],[f81,f68])).
% 2.03/0.63  fof(f68,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f11])).
% 2.03/0.63  fof(f11,axiom,(
% 2.03/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.03/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.03/0.63  fof(f106,plain,(
% 2.03/0.63    sK1 != sK2 | sK1 != k1_tarski(sK0)),
% 2.03/0.63    inference(inner_rewriting,[],[f105])).
% 2.03/0.63  fof(f105,plain,(
% 2.03/0.63    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 2.03/0.63    inference(inner_rewriting,[],[f58])).
% 2.03/0.63  fof(f58,plain,(
% 2.03/0.63    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.03/0.63    inference(cnf_transformation,[],[f40])).
% 2.03/0.63  fof(f1813,plain,(
% 2.03/0.63    r2_hidden(sK0,sK2) | r1_xboole_0(sK1,sK2)),
% 2.03/0.63    inference(superposition,[],[f76,f1812])).
% 2.03/0.63  fof(f1812,plain,(
% 2.03/0.63    sK0 = sK4(sK1,sK2)),
% 2.03/0.63    inference(subsumption_resolution,[],[f1811,f1489])).
% 2.03/0.63  fof(f1811,plain,(
% 2.03/0.63    sK0 = sK4(sK1,sK2) | k1_xboole_0 = sK2),
% 2.03/0.63    inference(resolution,[],[f1723,f224])).
% 2.03/0.63  fof(f1723,plain,(
% 2.03/0.63    ( ! [X0] : (r1_tarski(sK2,X0) | sK0 = sK4(sK1,sK2)) )),
% 2.03/0.63    inference(resolution,[],[f1605,f937])).
% 2.03/0.63  fof(f937,plain,(
% 2.03/0.63    ( ! [X8] : (r1_xboole_0(sK1,X8) | sK0 = sK4(sK1,X8)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f913,f160])).
% 2.03/0.63  fof(f913,plain,(
% 2.03/0.63    ( ! [X8] : (r1_xboole_0(sK1,X8) | sK0 = sK4(sK1,X8) | k1_xboole_0 = sK1) )),
% 2.03/0.63    inference(superposition,[],[f121,f884])).
% 2.03/0.63  fof(f121,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 2.03/0.63    inference(resolution,[],[f75,f104])).
% 2.03/0.63  fof(f1605,plain,(
% 2.03/0.63    ( ! [X3] : (~r1_xboole_0(sK1,sK2) | r1_tarski(sK2,X3)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f1106,f1575])).
% 2.03/0.63  fof(f1106,plain,(
% 2.03/0.63    ( ! [X3] : (r1_tarski(sK2,X3) | ~r1_xboole_0(sK1,sK2) | k1_xboole_0 = sK1) )),
% 2.03/0.63    inference(superposition,[],[f140,f933])).
% 2.03/0.63  % SZS output end Proof for theBenchmark
% 2.03/0.63  % (32608)------------------------------
% 2.03/0.63  % (32608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (32608)Termination reason: Refutation
% 2.03/0.63  
% 2.03/0.63  % (32608)Memory used [KB]: 7419
% 2.03/0.63  % (32608)Time elapsed: 0.207 s
% 2.03/0.63  % (32608)------------------------------
% 2.03/0.63  % (32608)------------------------------
% 2.03/0.63  % (32596)Success in time 0.273 s
%------------------------------------------------------------------------------
