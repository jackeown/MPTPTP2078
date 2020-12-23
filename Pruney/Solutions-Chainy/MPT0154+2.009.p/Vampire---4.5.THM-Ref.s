%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  124 (3738 expanded)
%              Number of leaves         :   20 ( 982 expanded)
%              Depth                    :   28
%              Number of atoms          :  379 (14095 expanded)
%              Number of equality atoms :  176 (4958 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1941,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1940])).

fof(f1940,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f227,f1899])).

fof(f1899,plain,(
    ! [X6,X5] : k5_xboole_0(X6,k5_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f1880,f1021])).

fof(f1021,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f997,f951])).

fof(f951,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f930,f115])).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f79,f104])).

fof(f104,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f50,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f930,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f822,f893])).

fof(f893,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f888,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f888,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f878,f616])).

fof(f616,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f204,f258])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f48])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f204,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(sK2(X7,X8),k5_xboole_0(X9,k3_xboole_0(X9,X7)))
      | k3_xboole_0(X7,X8) = X7 ) ),
    inference(resolution,[],[f121,f50])).

fof(f121,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(X6,X7)
      | ~ r2_hidden(sK2(X6,X7),k5_xboole_0(X8,k3_xboole_0(X8,X6))) ) ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f878,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) ) ),
    inference(superposition,[],[f204,f822])).

fof(f822,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f147,f163])).

fof(f163,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f145,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f145,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X4),X5)) = k5_xboole_0(X4,X5) ),
    inference(superposition,[],[f62,f115])).

fof(f147,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f62,f78])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f75])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f997,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f78,f970])).

fof(f970,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f888,f951])).

fof(f1880,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X6,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f1817,f1557])).

fof(f1557,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f1535,f62])).

fof(f1535,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f1534,f104])).

fof(f1534,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f1533,f969])).

fof(f969,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f912,f951])).

fof(f912,plain,(
    ! [X1] : ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f895,f163])).

fof(f895,plain,(
    ! [X1] : ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[],[f153,f888])).

fof(f153,plain,(
    ! [X12,X10,X11,X9] : ~ r2_hidden(X12,k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(k5_xboole_0(X9,X10),k2_tarski(X11,X12))))) ),
    inference(superposition,[],[f119,f62])).

fof(f119,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X2,X0)))) ),
    inference(resolution,[],[f96,f99])).

fof(f1533,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | r2_hidden(sK4(X0,X0,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f1516])).

fof(f1516,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | r2_hidden(sK4(X0,X0,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f1478,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f67,f48])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1478,plain,(
    ! [X45,X46] :
      ( r2_hidden(sK4(X45,X46,k1_xboole_0),X45)
      | k1_xboole_0 = k5_xboole_0(X45,k3_xboole_0(X45,X46)) ) ),
    inference(resolution,[],[f86,f969])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f66,f48])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1817,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f1559,f1789])).

fof(f1789,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f1762,f1021])).

fof(f1762,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f1559,f1535])).

fof(f1559,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f62,f1535])).

fof(f227,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f103,f210])).

fof(f210,plain,(
    ! [X2,X3] : k2_tarski(X2,X2) = k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X3)) ),
    inference(resolution,[],[f198,f101])).

fof(f101,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f198,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | k2_tarski(X5,X5) = k3_xboole_0(k2_tarski(X5,X5),X6) ) ),
    inference(resolution,[],[f195,f50])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(superposition,[],[f56,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( sK2(k2_tarski(X2,X2),X3) = X2
      | r1_tarski(k2_tarski(X2,X2),X3) ) ),
    inference(resolution,[],[f94,f55])).

fof(f94,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f77,f47])).

fof(f77,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f43,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f61,f75,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f43,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (2949)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (2950)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (2955)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (2964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (2965)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (2956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.58  % (2954)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (2960)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (2974)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (2953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.58  % (2959)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (2959)Refutation not found, incomplete strategy% (2959)------------------------------
% 0.22/0.58  % (2959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2959)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2959)Memory used [KB]: 10618
% 0.22/0.58  % (2959)Time elapsed: 0.151 s
% 0.22/0.58  % (2959)------------------------------
% 0.22/0.58  % (2959)------------------------------
% 1.49/0.59  % (2972)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.59  % (2972)Refutation not found, incomplete strategy% (2972)------------------------------
% 1.49/0.59  % (2972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (2972)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (2972)Memory used [KB]: 1663
% 1.49/0.59  % (2972)Time elapsed: 0.156 s
% 1.49/0.59  % (2972)------------------------------
% 1.49/0.59  % (2972)------------------------------
% 1.49/0.59  % (2973)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.60  % (2978)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.60  % (2952)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.60  % (2963)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.60  % (2977)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.60  % (2951)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.60  % (2951)Refutation not found, incomplete strategy% (2951)------------------------------
% 1.49/0.60  % (2951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (2951)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (2951)Memory used [KB]: 10746
% 1.49/0.60  % (2951)Time elapsed: 0.171 s
% 1.49/0.60  % (2951)------------------------------
% 1.49/0.60  % (2951)------------------------------
% 1.84/0.61  % (2975)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.84/0.61  % (2971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.84/0.61  % (2966)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.61  % (2971)Refutation not found, incomplete strategy% (2971)------------------------------
% 1.84/0.61  % (2971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (2971)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (2971)Memory used [KB]: 10746
% 1.84/0.61  % (2971)Time elapsed: 0.184 s
% 1.84/0.61  % (2971)------------------------------
% 1.84/0.61  % (2971)------------------------------
% 1.84/0.61  % (2970)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.84/0.61  % (2976)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.61  % (2962)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.84/0.61  % (2970)Refutation not found, incomplete strategy% (2970)------------------------------
% 1.84/0.61  % (2970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (2970)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (2970)Memory used [KB]: 1663
% 1.84/0.61  % (2970)Time elapsed: 0.183 s
% 1.84/0.61  % (2970)------------------------------
% 1.84/0.61  % (2970)------------------------------
% 1.84/0.61  % (2958)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.62  % (2967)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.84/0.62  % (2961)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.62  % (2968)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.84/0.63  % (2957)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.84/0.63  % (2957)Refutation not found, incomplete strategy% (2957)------------------------------
% 1.84/0.63  % (2957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.63  % (2957)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.63  
% 1.84/0.63  % (2957)Memory used [KB]: 10618
% 1.84/0.63  % (2957)Time elapsed: 0.203 s
% 1.84/0.63  % (2957)------------------------------
% 1.84/0.63  % (2957)------------------------------
% 1.84/0.63  % (2966)Refutation not found, incomplete strategy% (2966)------------------------------
% 1.84/0.63  % (2966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.63  % (2966)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.63  
% 1.84/0.63  % (2966)Memory used [KB]: 10618
% 1.84/0.63  % (2966)Time elapsed: 0.181 s
% 1.84/0.63  % (2966)------------------------------
% 1.84/0.63  % (2966)------------------------------
% 1.84/0.64  % (2969)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.84/0.65  % (2969)Refutation not found, incomplete strategy% (2969)------------------------------
% 1.84/0.65  % (2969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.65  % (2969)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.65  
% 1.84/0.65  % (2969)Memory used [KB]: 10746
% 1.84/0.65  % (2969)Time elapsed: 0.213 s
% 1.84/0.65  % (2969)------------------------------
% 1.84/0.65  % (2969)------------------------------
% 2.30/0.73  % (3019)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.30/0.74  % (2952)Refutation found. Thanks to Tanya!
% 2.30/0.74  % SZS status Theorem for theBenchmark
% 2.30/0.74  % SZS output start Proof for theBenchmark
% 2.30/0.74  fof(f1941,plain,(
% 2.30/0.74    $false),
% 2.30/0.74    inference(trivial_inequality_removal,[],[f1940])).
% 2.30/0.74  fof(f1940,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)),
% 2.30/0.74    inference(superposition,[],[f227,f1899])).
% 2.30/0.74  fof(f1899,plain,(
% 2.30/0.74    ( ! [X6,X5] : (k5_xboole_0(X6,k5_xboole_0(X5,X6)) = X5) )),
% 2.30/0.74    inference(forward_demodulation,[],[f1880,f1021])).
% 2.30/0.74  fof(f1021,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.30/0.74    inference(forward_demodulation,[],[f997,f951])).
% 2.30/0.74  fof(f951,plain,(
% 2.30/0.74    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.30/0.74    inference(forward_demodulation,[],[f930,f115])).
% 2.30/0.74  fof(f115,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 2.30/0.74    inference(forward_demodulation,[],[f79,f104])).
% 2.30/0.74  fof(f104,plain,(
% 2.30/0.74    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.30/0.74    inference(resolution,[],[f50,f90])).
% 2.30/0.74  fof(f90,plain,(
% 2.30/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.30/0.74    inference(equality_resolution,[],[f52])).
% 2.30/0.74  fof(f52,plain,(
% 2.30/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.30/0.74    inference(cnf_transformation,[],[f24])).
% 2.30/0.74  fof(f24,plain,(
% 2.30/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/0.74    inference(flattening,[],[f23])).
% 2.30/0.74  fof(f23,plain,(
% 2.30/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/0.74    inference(nnf_transformation,[],[f5])).
% 2.30/0.74  fof(f5,axiom,(
% 2.30/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.30/0.74  fof(f50,plain,(
% 2.30/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.30/0.74    inference(cnf_transformation,[],[f19])).
% 2.30/0.74  fof(f19,plain,(
% 2.30/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.30/0.74    inference(ennf_transformation,[],[f8])).
% 2.30/0.74  fof(f8,axiom,(
% 2.30/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.30/0.74  fof(f79,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.30/0.74    inference(definition_unfolding,[],[f46,f75])).
% 2.30/0.74  fof(f75,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.30/0.74    inference(definition_unfolding,[],[f49,f48])).
% 2.30/0.74  fof(f48,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.30/0.74    inference(cnf_transformation,[],[f6])).
% 2.30/0.74  fof(f6,axiom,(
% 2.30/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.30/0.74  fof(f49,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.30/0.74    inference(cnf_transformation,[],[f10])).
% 2.30/0.74  fof(f10,axiom,(
% 2.30/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.30/0.74  fof(f46,plain,(
% 2.30/0.74    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.30/0.74    inference(cnf_transformation,[],[f17])).
% 2.30/0.74  fof(f17,plain,(
% 2.30/0.74    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.30/0.74    inference(rectify,[],[f4])).
% 2.30/0.74  fof(f4,axiom,(
% 2.30/0.74    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.30/0.74  fof(f930,plain,(
% 2.30/0.74    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 2.30/0.74    inference(backward_demodulation,[],[f822,f893])).
% 2.30/0.74  fof(f893,plain,(
% 2.30/0.74    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.30/0.74    inference(superposition,[],[f888,f47])).
% 2.30/0.74  fof(f47,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f1])).
% 2.30/0.74  fof(f1,axiom,(
% 2.30/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.30/0.74  fof(f888,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 2.30/0.74    inference(subsumption_resolution,[],[f878,f616])).
% 2.30/0.74  fof(f616,plain,(
% 2.30/0.74    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k3_xboole_0(X0,X1) = X0) )),
% 2.30/0.74    inference(resolution,[],[f204,f258])).
% 2.30/0.74  fof(f258,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(k2_tarski(X2,X0),k3_xboole_0(k2_tarski(X2,X0),X1))) | r2_hidden(X0,X1)) )),
% 2.30/0.74    inference(resolution,[],[f95,f99])).
% 2.30/0.74  fof(f99,plain,(
% 2.30/0.74    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.30/0.74    inference(equality_resolution,[],[f98])).
% 2.30/0.74  fof(f98,plain,(
% 2.30/0.74    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.30/0.74    inference(equality_resolution,[],[f71])).
% 2.30/0.74  fof(f71,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.30/0.74    inference(cnf_transformation,[],[f42])).
% 2.30/0.74  fof(f42,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 2.30/0.74  fof(f41,plain,(
% 2.30/0.74    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.30/0.74    introduced(choice_axiom,[])).
% 2.30/0.74  fof(f40,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.74    inference(rectify,[],[f39])).
% 2.30/0.74  fof(f39,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.74    inference(flattening,[],[f38])).
% 2.30/0.74  fof(f38,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.74    inference(nnf_transformation,[],[f12])).
% 2.30/0.74  fof(f12,axiom,(
% 2.30/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.30/0.74  fof(f95,plain,(
% 2.30/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.30/0.74    inference(equality_resolution,[],[f87])).
% 2.30/0.74  fof(f87,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.30/0.74    inference(definition_unfolding,[],[f65,f48])).
% 2.30/0.74  fof(f65,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.74    inference(cnf_transformation,[],[f37])).
% 2.30/0.74  fof(f37,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.30/0.74  fof(f36,plain,(
% 2.30/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.30/0.74    introduced(choice_axiom,[])).
% 2.30/0.74  fof(f35,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.74    inference(rectify,[],[f34])).
% 2.30/0.74  fof(f34,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.74    inference(flattening,[],[f33])).
% 2.30/0.74  fof(f33,plain,(
% 2.30/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.74    inference(nnf_transformation,[],[f3])).
% 2.30/0.74  fof(f3,axiom,(
% 2.30/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.30/0.74  fof(f204,plain,(
% 2.30/0.74    ( ! [X8,X7,X9] : (~r2_hidden(sK2(X7,X8),k5_xboole_0(X9,k3_xboole_0(X9,X7))) | k3_xboole_0(X7,X8) = X7) )),
% 2.30/0.74    inference(resolution,[],[f121,f50])).
% 2.30/0.74  fof(f121,plain,(
% 2.30/0.74    ( ! [X6,X8,X7] : (r1_tarski(X6,X7) | ~r2_hidden(sK2(X6,X7),k5_xboole_0(X8,k3_xboole_0(X8,X6)))) )),
% 2.30/0.74    inference(resolution,[],[f96,f55])).
% 2.30/0.74  fof(f55,plain,(
% 2.30/0.74    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f28])).
% 2.30/0.74  fof(f28,plain,(
% 2.30/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 2.30/0.74  fof(f27,plain,(
% 2.30/0.74    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.30/0.74    introduced(choice_axiom,[])).
% 2.30/0.74  fof(f26,plain,(
% 2.30/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.74    inference(rectify,[],[f25])).
% 2.30/0.74  fof(f25,plain,(
% 2.30/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.30/0.74    inference(nnf_transformation,[],[f20])).
% 2.30/0.74  fof(f20,plain,(
% 2.30/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.30/0.74    inference(ennf_transformation,[],[f2])).
% 2.30/0.74  fof(f2,axiom,(
% 2.30/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.30/0.74  fof(f96,plain,(
% 2.30/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.30/0.74    inference(equality_resolution,[],[f88])).
% 2.30/0.74  fof(f88,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.30/0.74    inference(definition_unfolding,[],[f64,f48])).
% 2.30/0.74  fof(f64,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.74    inference(cnf_transformation,[],[f37])).
% 2.30/0.74  fof(f878,plain,(
% 2.30/0.74    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0),k5_xboole_0(k1_xboole_0,k1_xboole_0)) | k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 2.30/0.74    inference(superposition,[],[f204,f822])).
% 2.30/0.74  fof(f822,plain,(
% 2.30/0.74    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))),
% 2.30/0.74    inference(superposition,[],[f147,f163])).
% 2.30/0.74  fof(f163,plain,(
% 2.30/0.74    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X5)))) )),
% 2.30/0.74    inference(forward_demodulation,[],[f145,f62])).
% 2.30/0.74  fof(f62,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.30/0.74    inference(cnf_transformation,[],[f9])).
% 2.30/0.74  fof(f9,axiom,(
% 2.30/0.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.30/0.74  fof(f145,plain,(
% 2.30/0.74    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X4,X4),X5)) = k5_xboole_0(X4,X5)) )),
% 2.30/0.74    inference(superposition,[],[f62,f115])).
% 2.30/0.74  fof(f147,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)))))) )),
% 2.30/0.74    inference(superposition,[],[f62,f78])).
% 2.30/0.74  fof(f78,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.30/0.74    inference(definition_unfolding,[],[f44,f75])).
% 2.30/0.74  fof(f44,plain,(
% 2.30/0.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.30/0.74    inference(cnf_transformation,[],[f7])).
% 2.30/0.74  fof(f7,axiom,(
% 2.30/0.74    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.30/0.74  fof(f997,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 2.30/0.74    inference(backward_demodulation,[],[f78,f970])).
% 2.30/0.74  fof(f970,plain,(
% 2.30/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.30/0.74    inference(backward_demodulation,[],[f888,f951])).
% 2.30/0.74  fof(f1880,plain,(
% 2.30/0.74    ( ! [X6,X5] : (k5_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X6,k5_xboole_0(X5,X6))) )),
% 2.30/0.74    inference(superposition,[],[f1817,f1557])).
% 2.30/0.74  fof(f1557,plain,(
% 2.30/0.74    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 2.30/0.74    inference(superposition,[],[f1535,f62])).
% 2.30/0.74  fof(f1535,plain,(
% 2.30/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.30/0.74    inference(forward_demodulation,[],[f1534,f104])).
% 2.30/0.74  fof(f1534,plain,(
% 2.30/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.30/0.74    inference(subsumption_resolution,[],[f1533,f969])).
% 2.30/0.74  fof(f969,plain,(
% 2.30/0.74    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.30/0.74    inference(backward_demodulation,[],[f912,f951])).
% 2.30/0.74  fof(f912,plain,(
% 2.30/0.74    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.30/0.74    inference(forward_demodulation,[],[f895,f163])).
% 2.30/0.74  fof(f895,plain,(
% 2.30/0.74    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) )),
% 2.30/0.74    inference(superposition,[],[f153,f888])).
% 2.30/0.74  fof(f153,plain,(
% 2.30/0.74    ( ! [X12,X10,X11,X9] : (~r2_hidden(X12,k5_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(k5_xboole_0(X9,X10),k2_tarski(X11,X12)))))) )),
% 2.30/0.74    inference(superposition,[],[f119,f62])).
% 2.30/0.74  fof(f119,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X2,X0))))) )),
% 2.30/0.74    inference(resolution,[],[f96,f99])).
% 2.30/0.74  fof(f1533,plain,(
% 2.30/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | r2_hidden(sK4(X0,X0,k1_xboole_0),k1_xboole_0)) )),
% 2.30/0.74    inference(duplicate_literal_removal,[],[f1516])).
% 2.30/0.74  fof(f1516,plain,(
% 2.30/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | r2_hidden(sK4(X0,X0,k1_xboole_0),k1_xboole_0)) )),
% 2.30/0.74    inference(resolution,[],[f1478,f85])).
% 2.30/0.74  fof(f85,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.74    inference(definition_unfolding,[],[f67,f48])).
% 2.30/0.74  fof(f67,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f37])).
% 2.30/0.74  fof(f1478,plain,(
% 2.30/0.74    ( ! [X45,X46] : (r2_hidden(sK4(X45,X46,k1_xboole_0),X45) | k1_xboole_0 = k5_xboole_0(X45,k3_xboole_0(X45,X46))) )),
% 2.30/0.74    inference(resolution,[],[f86,f969])).
% 2.30/0.74  fof(f86,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.30/0.74    inference(definition_unfolding,[],[f66,f48])).
% 2.30/0.74  fof(f66,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f37])).
% 2.30/0.74  fof(f1817,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.30/0.74    inference(backward_demodulation,[],[f1559,f1789])).
% 2.30/0.74  fof(f1789,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.30/0.74    inference(forward_demodulation,[],[f1762,f1021])).
% 2.30/0.74  fof(f1762,plain,(
% 2.30/0.74    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.30/0.74    inference(superposition,[],[f1559,f1535])).
% 2.30/0.74  fof(f1559,plain,(
% 2.30/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.30/0.74    inference(superposition,[],[f62,f1535])).
% 2.30/0.74  fof(f227,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 2.30/0.74    inference(backward_demodulation,[],[f103,f210])).
% 2.30/0.74  fof(f210,plain,(
% 2.30/0.74    ( ! [X2,X3] : (k2_tarski(X2,X2) = k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X3))) )),
% 2.30/0.74    inference(resolution,[],[f198,f101])).
% 2.30/0.74  fof(f101,plain,(
% 2.30/0.74    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.30/0.74    inference(equality_resolution,[],[f100])).
% 2.30/0.74  fof(f100,plain,(
% 2.30/0.74    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.30/0.74    inference(equality_resolution,[],[f70])).
% 2.30/0.74  fof(f70,plain,(
% 2.30/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.30/0.74    inference(cnf_transformation,[],[f42])).
% 2.30/0.74  fof(f198,plain,(
% 2.30/0.74    ( ! [X6,X5] : (~r2_hidden(X5,X6) | k2_tarski(X5,X5) = k3_xboole_0(k2_tarski(X5,X5),X6)) )),
% 2.30/0.74    inference(resolution,[],[f195,f50])).
% 2.30/0.74  fof(f195,plain,(
% 2.30/0.74    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.30/0.74    inference(duplicate_literal_removal,[],[f192])).
% 2.30/0.74  fof(f192,plain,(
% 2.30/0.74    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 2.30/0.74    inference(superposition,[],[f56,f109])).
% 2.30/0.74  fof(f109,plain,(
% 2.30/0.74    ( ! [X2,X3] : (sK2(k2_tarski(X2,X2),X3) = X2 | r1_tarski(k2_tarski(X2,X2),X3)) )),
% 2.30/0.74    inference(resolution,[],[f94,f55])).
% 2.30/0.74  fof(f94,plain,(
% 2.30/0.74    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 2.30/0.74    inference(equality_resolution,[],[f83])).
% 2.30/0.74  fof(f83,plain,(
% 2.30/0.74    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 2.30/0.74    inference(definition_unfolding,[],[f57,f45])).
% 2.30/0.74  fof(f45,plain,(
% 2.30/0.74    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f14])).
% 2.30/0.74  fof(f14,axiom,(
% 2.30/0.74    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.30/0.74  fof(f57,plain,(
% 2.30/0.74    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.30/0.74    inference(cnf_transformation,[],[f32])).
% 2.30/0.74  fof(f32,plain,(
% 2.30/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 2.30/0.74  fof(f31,plain,(
% 2.30/0.74    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.30/0.74    introduced(choice_axiom,[])).
% 2.30/0.74  fof(f30,plain,(
% 2.30/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.74    inference(rectify,[],[f29])).
% 2.30/0.74  fof(f29,plain,(
% 2.30/0.74    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.74    inference(nnf_transformation,[],[f11])).
% 2.30/0.74  fof(f11,axiom,(
% 2.30/0.74    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.30/0.74  fof(f56,plain,(
% 2.30/0.74    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.30/0.74    inference(cnf_transformation,[],[f28])).
% 2.30/0.74  fof(f103,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))))),
% 2.30/0.74    inference(forward_demodulation,[],[f77,f47])).
% 2.30/0.74  fof(f77,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))))),
% 2.30/0.74    inference(definition_unfolding,[],[f43,f76])).
% 2.30/0.74  fof(f76,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 2.30/0.74    inference(definition_unfolding,[],[f61,f75,f45])).
% 2.30/0.74  fof(f61,plain,(
% 2.30/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.30/0.74    inference(cnf_transformation,[],[f13])).
% 2.30/0.74  fof(f13,axiom,(
% 2.30/0.74    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 2.30/0.74  fof(f43,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.30/0.74    inference(cnf_transformation,[],[f22])).
% 2.30/0.74  fof(f22,plain,(
% 2.30/0.74    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.30/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21])).
% 2.30/0.74  fof(f21,plain,(
% 2.30/0.74    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.30/0.74    introduced(choice_axiom,[])).
% 2.30/0.74  fof(f18,plain,(
% 2.30/0.74    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 2.30/0.74    inference(ennf_transformation,[],[f16])).
% 2.30/0.74  fof(f16,negated_conjecture,(
% 2.30/0.74    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.30/0.74    inference(negated_conjecture,[],[f15])).
% 2.30/0.74  fof(f15,conjecture,(
% 2.30/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.30/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.30/0.74  % SZS output end Proof for theBenchmark
% 2.30/0.74  % (2952)------------------------------
% 2.30/0.74  % (2952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.74  % (2952)Termination reason: Refutation
% 2.30/0.74  
% 2.30/0.74  % (2952)Memory used [KB]: 12153
% 2.30/0.74  % (2952)Time elapsed: 0.307 s
% 2.30/0.74  % (2952)------------------------------
% 2.30/0.74  % (2952)------------------------------
% 2.83/0.76  % (3017)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.83/0.76  % (2948)Success in time 0.39 s
%------------------------------------------------------------------------------
