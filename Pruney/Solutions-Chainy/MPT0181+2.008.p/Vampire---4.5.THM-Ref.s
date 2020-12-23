%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 899 expanded)
%              Number of leaves         :   10 ( 260 expanded)
%              Depth                    :   26
%              Number of atoms          :  203 (4178 expanded)
%              Number of equality atoms :   56 ( 511 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1749,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f1732])).

fof(f1732,plain,(
    ! [X17,X18,X16] : k1_enumset1(X16,X18,X17) = k1_enumset1(X16,X17,X18) ),
    inference(superposition,[],[f1643,f787])).

fof(f787,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3) ),
    inference(forward_demodulation,[],[f771,f745])).

fof(f745,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f733,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f106,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f106,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f35,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f733,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(backward_demodulation,[],[f190,f718])).

fof(f718,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f692,f109])).

fof(f692,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X25)) ),
    inference(superposition,[],[f662,f110])).

fof(f110,plain,(
    ! [X4,X3] : k2_tarski(X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f107,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f40,f23])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f38,f24])).

fof(f107,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_enumset1(X3,X3,X3,X4) ),
    inference(superposition,[],[f35,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f61,f24])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f44,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f38,f22])).

fof(f662,plain,(
    ! [X14,X13] : k2_xboole_0(X13,X14) = k2_xboole_0(k2_xboole_0(X13,X14),X14) ),
    inference(resolution,[],[f657,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f657,plain,(
    ! [X0,X1] : sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f656,f239])).

fof(f239,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5,X5),X4)
      | sP0(X4,X5,X5) ) ),
    inference(subsumption_resolution,[],[f231,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f231,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5,X5),X4)
      | r2_hidden(sK4(X4,X5,X5),X5)
      | sP0(X4,X5,X5) ) ),
    inference(factoring,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f656,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)
      | sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f608,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f608,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X2,X0))
      | sP0(X0,X1,X1) ) ),
    inference(resolution,[],[f255,f36])).

fof(f36,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f255,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X6,X9,X8)
      | r2_hidden(sK4(X6,X7,X7),X8)
      | sP0(X6,X7,X7) ) ),
    inference(resolution,[],[f239,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f190,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2)) ),
    inference(resolution,[],[f160,f32])).

fof(f160,plain,(
    ! [X4,X5,X3] : sP0(k1_tarski(X5),k1_enumset1(X3,X4,X4),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5))) ),
    inference(superposition,[],[f108,f38])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : sP0(k1_tarski(X3),k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f36,f35])).

fof(f771,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f34,f718])).

fof(f1643,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X3,X2) ),
    inference(forward_demodulation,[],[f1610,f745])).

fof(f1610,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f34,f1590])).

fof(f1590,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f1540,f109])).

fof(f1540,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ),
    inference(resolution,[],[f1535,f32])).

fof(f1535,plain,(
    ! [X6,X5] : sP0(k1_tarski(X5),k2_tarski(X6,X5),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f1353,f1332])).

fof(f1332,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f1297,f109])).

fof(f1297,plain,(
    ! [X28,X27] : k2_tarski(X27,X28) = k2_xboole_0(k2_tarski(X27,X28),k1_tarski(X27)) ),
    inference(superposition,[],[f1226,f44])).

fof(f1226,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f1225,f32])).

fof(f1225,plain,(
    ! [X0,X1] : sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f1224,f239])).

fof(f1224,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f1195])).

fof(f1195,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0)
      | sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f1166,f30])).

fof(f1166,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X0,X2))
      | sP0(X0,X1,X1) ) ),
    inference(resolution,[],[f256,f36])).

fof(f256,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ sP0(X13,X10,X12)
      | r2_hidden(sK4(X10,X11,X11),X12)
      | sP0(X10,X11,X11) ) ),
    inference(resolution,[],[f239,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1353,plain,(
    ! [X12,X10,X11] : sP0(k1_tarski(X12),k2_tarski(X11,X10),k1_enumset1(X10,X11,X12)) ),
    inference(superposition,[],[f129,f1333])).

fof(f1333,plain,(
    ! [X6,X5] : k2_tarski(X6,X5) = k2_tarski(X5,X6) ),
    inference(superposition,[],[f1297,f735])).

fof(f735,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X3)) ),
    inference(backward_demodulation,[],[f351,f718])).

fof(f351,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k2_xboole_0(k1_enumset1(X3,X4,X4),k1_tarski(X3)) ),
    inference(resolution,[],[f334,f32])).

fof(f334,plain,(
    ! [X0,X1] : sP0(k1_tarski(X0),k1_enumset1(X0,X1,X1),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f160,f321])).

fof(f321,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_xboole_0(k1_tarski(X16),k2_tarski(X15,X16)) ),
    inference(superposition,[],[f304,f110])).

fof(f304,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(resolution,[],[f302,f32])).

fof(f302,plain,(
    ! [X0,X1] : sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f301,f274])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),k2_xboole_0(X2,X1))
      | sP0(X0,X1,X0) ) ),
    inference(resolution,[],[f243,f36])).

fof(f243,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X7,X9,X8)
      | r2_hidden(sK4(X6,X7,X6),X8)
      | sP0(X6,X7,X6) ) ),
    inference(resolution,[],[f238,f27])).

fof(f238,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(subsumption_resolution,[],[f230,f30])).

fof(f230,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X2)
      | r2_hidden(sK4(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(factoring,[],[f28])).

fof(f301,plain,(
    ! [X0,X1] :
      ( sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1))
      | sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f274,f30])).

fof(f129,plain,(
    ! [X2,X0,X1] : sP0(k1_tarski(X2),k2_tarski(X0,X1),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f36,f109])).

fof(f21,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (20440)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (20411)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20422)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (20413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20413)Refutation not found, incomplete strategy% (20413)------------------------------
% 0.21/0.52  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20413)Memory used [KB]: 6140
% 0.21/0.52  % (20413)Time elapsed: 0.100 s
% 0.21/0.52  % (20413)------------------------------
% 0.21/0.52  % (20413)------------------------------
% 0.21/0.52  % (20426)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (20415)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (20436)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (20424)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (20420)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20436)Refutation not found, incomplete strategy% (20436)------------------------------
% 0.21/0.53  % (20436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20411)Refutation not found, incomplete strategy% (20411)------------------------------
% 0.21/0.53  % (20411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20411)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20411)Memory used [KB]: 10618
% 0.21/0.53  % (20411)Time elapsed: 0.110 s
% 0.21/0.53  % (20411)------------------------------
% 0.21/0.53  % (20411)------------------------------
% 0.21/0.53  % (20420)Refutation not found, incomplete strategy% (20420)------------------------------
% 0.21/0.53  % (20420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20420)Memory used [KB]: 10618
% 0.21/0.53  % (20420)Time elapsed: 0.116 s
% 0.21/0.53  % (20420)------------------------------
% 0.21/0.53  % (20420)------------------------------
% 0.21/0.54  % (20436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20436)Memory used [KB]: 6140
% 0.21/0.54  % (20436)Time elapsed: 0.063 s
% 0.21/0.54  % (20436)------------------------------
% 0.21/0.54  % (20436)------------------------------
% 0.21/0.54  % (20416)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (20410)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20412)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (20409)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (20409)Refutation not found, incomplete strategy% (20409)------------------------------
% 0.21/0.54  % (20409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20409)Memory used [KB]: 1663
% 0.21/0.54  % (20409)Time elapsed: 0.124 s
% 0.21/0.54  % (20409)------------------------------
% 0.21/0.54  % (20409)------------------------------
% 0.21/0.54  % (20417)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (20417)Refutation not found, incomplete strategy% (20417)------------------------------
% 0.21/0.54  % (20417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20417)Memory used [KB]: 10618
% 0.21/0.54  % (20417)Time elapsed: 0.133 s
% 0.21/0.54  % (20417)------------------------------
% 0.21/0.54  % (20417)------------------------------
% 0.21/0.55  % (20428)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (20439)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (20437)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (20434)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (20434)Refutation not found, incomplete strategy% (20434)------------------------------
% 0.21/0.55  % (20434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20434)Memory used [KB]: 1663
% 0.21/0.55  % (20434)Time elapsed: 0.138 s
% 0.21/0.55  % (20434)------------------------------
% 0.21/0.55  % (20434)------------------------------
% 0.21/0.55  % (20437)Refutation not found, incomplete strategy% (20437)------------------------------
% 0.21/0.55  % (20437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20437)Memory used [KB]: 10618
% 0.21/0.55  % (20437)Time elapsed: 0.137 s
% 0.21/0.55  % (20437)------------------------------
% 0.21/0.55  % (20437)------------------------------
% 0.21/0.55  % (20430)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (20430)Refutation not found, incomplete strategy% (20430)------------------------------
% 0.21/0.55  % (20430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20430)Memory used [KB]: 10618
% 0.21/0.55  % (20430)Time elapsed: 0.149 s
% 0.21/0.55  % (20430)------------------------------
% 0.21/0.55  % (20430)------------------------------
% 0.21/0.55  % (20421)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (20419)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (20421)Refutation not found, incomplete strategy% (20421)------------------------------
% 0.21/0.56  % (20421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20421)Memory used [KB]: 10618
% 0.21/0.56  % (20421)Time elapsed: 0.148 s
% 0.21/0.56  % (20421)------------------------------
% 0.21/0.56  % (20421)------------------------------
% 0.21/0.56  % (20419)Refutation not found, incomplete strategy% (20419)------------------------------
% 0.21/0.56  % (20419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20419)Memory used [KB]: 10618
% 0.21/0.56  % (20419)Time elapsed: 0.150 s
% 0.21/0.56  % (20419)------------------------------
% 0.21/0.56  % (20419)------------------------------
% 0.21/0.56  % (20438)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (20431)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (20431)Refutation not found, incomplete strategy% (20431)------------------------------
% 0.21/0.56  % (20431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20431)Memory used [KB]: 1663
% 0.21/0.56  % (20431)Time elapsed: 0.147 s
% 0.21/0.56  % (20431)------------------------------
% 0.21/0.56  % (20431)------------------------------
% 0.21/0.56  % (20427)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (20427)Refutation not found, incomplete strategy% (20427)------------------------------
% 0.21/0.56  % (20427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20427)Memory used [KB]: 10618
% 0.21/0.56  % (20427)Time elapsed: 0.147 s
% 0.21/0.56  % (20427)------------------------------
% 0.21/0.56  % (20427)------------------------------
% 0.21/0.56  % (20425)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (20425)Refutation not found, incomplete strategy% (20425)------------------------------
% 0.21/0.56  % (20425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20425)Memory used [KB]: 6140
% 0.21/0.56  % (20425)Time elapsed: 0.001 s
% 0.21/0.56  % (20425)------------------------------
% 0.21/0.56  % (20425)------------------------------
% 0.21/0.56  % (20414)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (20429)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (20423)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (20435)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (20433)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (20433)Refutation not found, incomplete strategy% (20433)------------------------------
% 0.21/0.59  % (20433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (20433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (20433)Memory used [KB]: 10618
% 0.21/0.60  % (20433)Time elapsed: 0.178 s
% 0.21/0.60  % (20433)------------------------------
% 0.21/0.60  % (20433)------------------------------
% 0.21/0.65  % (20454)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.65  % (20416)Refutation found. Thanks to Tanya!
% 0.21/0.65  % SZS status Theorem for theBenchmark
% 0.21/0.65  % (20454)Refutation not found, incomplete strategy% (20454)------------------------------
% 0.21/0.65  % (20454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.65  % (20454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.65  
% 0.21/0.65  % (20454)Memory used [KB]: 6140
% 0.21/0.65  % (20454)Time elapsed: 0.098 s
% 0.21/0.65  % (20454)------------------------------
% 0.21/0.65  % (20454)------------------------------
% 0.21/0.66  % (20457)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 0.21/0.66  % (20458)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 0.21/0.67  % (20458)Refutation not found, incomplete strategy% (20458)------------------------------
% 0.21/0.67  % (20458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.67  % (20458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.67  
% 0.21/0.67  % (20458)Memory used [KB]: 10618
% 0.21/0.67  % (20458)Time elapsed: 0.099 s
% 0.21/0.67  % (20458)------------------------------
% 0.21/0.67  % (20458)------------------------------
% 0.21/0.67  % SZS output start Proof for theBenchmark
% 0.21/0.67  fof(f1749,plain,(
% 0.21/0.67    $false),
% 0.21/0.67    inference(subsumption_resolution,[],[f21,f1732])).
% 0.21/0.67  fof(f1732,plain,(
% 0.21/0.67    ( ! [X17,X18,X16] : (k1_enumset1(X16,X18,X17) = k1_enumset1(X16,X17,X18)) )),
% 0.21/0.67    inference(superposition,[],[f1643,f787])).
% 0.21/0.67  fof(f787,plain,(
% 0.21/0.67    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3)) )),
% 0.21/0.67    inference(forward_demodulation,[],[f771,f745])).
% 0.21/0.67  fof(f745,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.67    inference(forward_demodulation,[],[f733,f109])).
% 0.21/0.67  fof(f109,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.67    inference(forward_demodulation,[],[f106,f24])).
% 0.21/0.67  fof(f24,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f6])).
% 0.21/0.67  fof(f6,axiom,(
% 0.21/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.67  fof(f106,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.67    inference(superposition,[],[f35,f23])).
% 0.21/0.67  fof(f23,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f5])).
% 0.21/0.67  fof(f5,axiom,(
% 0.21/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.67  fof(f35,plain,(
% 0.21/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.67    inference(cnf_transformation,[],[f3])).
% 0.21/0.67  fof(f3,axiom,(
% 0.21/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.67  fof(f733,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.67    inference(backward_demodulation,[],[f190,f718])).
% 0.21/0.67  fof(f718,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 0.21/0.67    inference(superposition,[],[f692,f109])).
% 0.21/0.67  fof(f692,plain,(
% 0.21/0.67    ( ! [X24,X25] : (k2_tarski(X24,X25) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X25))) )),
% 0.21/0.67    inference(superposition,[],[f662,f110])).
% 0.21/0.67  fof(f110,plain,(
% 0.21/0.67    ( ! [X4,X3] : (k2_tarski(X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) )),
% 0.21/0.67    inference(forward_demodulation,[],[f107,f47])).
% 0.21/0.67  fof(f47,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.67    inference(superposition,[],[f44,f38])).
% 0.21/0.67  fof(f38,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.21/0.67    inference(superposition,[],[f34,f23])).
% 0.21/0.67  fof(f34,plain,(
% 0.21/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.67    inference(cnf_transformation,[],[f2])).
% 0.21/0.67  fof(f2,axiom,(
% 0.21/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.67  fof(f44,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.67    inference(forward_demodulation,[],[f40,f23])).
% 0.21/0.67  fof(f40,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.67    inference(superposition,[],[f38,f24])).
% 0.21/0.67  fof(f107,plain,(
% 0.21/0.67    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_enumset1(X3,X3,X3,X4)) )),
% 0.21/0.67    inference(superposition,[],[f35,f73])).
% 0.21/0.67  fof(f73,plain,(
% 0.21/0.67    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.67    inference(superposition,[],[f61,f24])).
% 0.21/0.67  fof(f61,plain,(
% 0.21/0.67    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.67    inference(superposition,[],[f41,f46])).
% 0.21/0.67  fof(f46,plain,(
% 0.21/0.67    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.67    inference(superposition,[],[f44,f22])).
% 0.21/0.67  fof(f22,plain,(
% 0.21/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f4])).
% 0.21/0.67  fof(f4,axiom,(
% 0.21/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.67  fof(f41,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.21/0.67    inference(superposition,[],[f38,f22])).
% 0.21/0.67  fof(f662,plain,(
% 0.21/0.67    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k2_xboole_0(k2_xboole_0(X13,X14),X14)) )),
% 0.21/0.67    inference(resolution,[],[f657,f32])).
% 0.21/0.67  fof(f32,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.67    inference(cnf_transformation,[],[f20])).
% 0.21/0.67  fof(f20,plain,(
% 0.21/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.67    inference(nnf_transformation,[],[f12])).
% 0.21/0.67  fof(f12,plain,(
% 0.21/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.67    inference(definition_folding,[],[f1,f11])).
% 0.21/0.67  fof(f11,plain,(
% 0.21/0.67    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.67  fof(f1,axiom,(
% 0.21/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.67  fof(f657,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 0.21/0.67    inference(subsumption_resolution,[],[f656,f239])).
% 0.21/0.67  fof(f239,plain,(
% 0.21/0.67    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5,X5),X4) | sP0(X4,X5,X5)) )),
% 0.21/0.67    inference(subsumption_resolution,[],[f231,f29])).
% 0.21/0.67  fof(f29,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f19])).
% 0.21/0.67  fof(f19,plain,(
% 0.21/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.21/0.67  fof(f18,plain,(
% 0.21/0.67    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.67    introduced(choice_axiom,[])).
% 0.21/0.67  fof(f17,plain,(
% 0.21/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.67    inference(rectify,[],[f16])).
% 0.21/0.67  fof(f16,plain,(
% 0.21/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.67    inference(flattening,[],[f15])).
% 0.21/0.67  fof(f15,plain,(
% 0.21/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.67    inference(nnf_transformation,[],[f11])).
% 0.21/0.67  fof(f231,plain,(
% 0.21/0.67    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5,X5),X4) | r2_hidden(sK4(X4,X5,X5),X5) | sP0(X4,X5,X5)) )),
% 0.21/0.67    inference(factoring,[],[f28])).
% 0.21/0.67  fof(f28,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f19])).
% 0.21/0.67  fof(f656,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) | ~r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)) )),
% 0.21/0.67    inference(duplicate_literal_removal,[],[f631])).
% 0.21/0.67  fof(f631,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) | ~r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) | sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 0.21/0.67    inference(resolution,[],[f608,f30])).
% 0.21/0.67  fof(f30,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f19])).
% 0.21/0.67  fof(f608,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X2,X0)) | sP0(X0,X1,X1)) )),
% 0.21/0.67    inference(resolution,[],[f255,f36])).
% 0.21/0.67  fof(f36,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(equality_resolution,[],[f31])).
% 0.21/0.67  fof(f31,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.67    inference(cnf_transformation,[],[f20])).
% 0.21/0.67  fof(f255,plain,(
% 0.21/0.67    ( ! [X6,X8,X7,X9] : (~sP0(X6,X9,X8) | r2_hidden(sK4(X6,X7,X7),X8) | sP0(X6,X7,X7)) )),
% 0.21/0.67    inference(resolution,[],[f239,f27])).
% 0.21/0.67  fof(f27,plain,(
% 0.21/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f19])).
% 0.21/0.67  fof(f190,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2))) )),
% 0.21/0.67    inference(resolution,[],[f160,f32])).
% 0.21/0.67  fof(f160,plain,(
% 0.21/0.67    ( ! [X4,X5,X3] : (sP0(k1_tarski(X5),k1_enumset1(X3,X4,X4),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)))) )),
% 0.21/0.67    inference(superposition,[],[f108,f38])).
% 0.21/0.67  fof(f108,plain,(
% 0.21/0.67    ( ! [X2,X0,X3,X1] : (sP0(k1_tarski(X3),k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.67    inference(superposition,[],[f36,f35])).
% 0.21/0.67  fof(f771,plain,(
% 0.21/0.67    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))) )),
% 0.21/0.67    inference(superposition,[],[f34,f718])).
% 0.21/0.67  fof(f1643,plain,(
% 0.21/0.67    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X3,X2)) )),
% 0.21/0.67    inference(forward_demodulation,[],[f1610,f745])).
% 0.21/0.67  fof(f1610,plain,(
% 0.21/0.67    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2))) )),
% 0.21/0.67    inference(superposition,[],[f34,f1590])).
% 0.21/0.67  fof(f1590,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 0.21/0.67    inference(superposition,[],[f1540,f109])).
% 0.21/0.67  fof(f1540,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))) )),
% 0.21/0.67    inference(resolution,[],[f1535,f32])).
% 0.21/0.67  fof(f1535,plain,(
% 0.21/0.67    ( ! [X6,X5] : (sP0(k1_tarski(X5),k2_tarski(X6,X5),k2_tarski(X5,X6))) )),
% 0.21/0.67    inference(superposition,[],[f1353,f1332])).
% 0.21/0.67  fof(f1332,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.67    inference(superposition,[],[f1297,f109])).
% 0.21/0.67  fof(f1297,plain,(
% 0.21/0.67    ( ! [X28,X27] : (k2_tarski(X27,X28) = k2_xboole_0(k2_tarski(X27,X28),k1_tarski(X27))) )),
% 0.21/0.67    inference(superposition,[],[f1226,f44])).
% 0.21/0.67  fof(f1226,plain,(
% 0.21/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 0.21/0.67    inference(resolution,[],[f1225,f32])).
% 0.21/0.67  fof(f1225,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(subsumption_resolution,[],[f1224,f239])).
% 0.21/0.67  fof(f1224,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0)) )),
% 0.21/0.67    inference(duplicate_literal_removal,[],[f1195])).
% 0.21/0.67  fof(f1195,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0) | sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(resolution,[],[f1166,f30])).
% 0.21/0.67  fof(f1166,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X0,X2)) | sP0(X0,X1,X1)) )),
% 0.21/0.67    inference(resolution,[],[f256,f36])).
% 0.21/0.67  fof(f256,plain,(
% 0.21/0.67    ( ! [X12,X10,X13,X11] : (~sP0(X13,X10,X12) | r2_hidden(sK4(X10,X11,X11),X12) | sP0(X10,X11,X11)) )),
% 0.21/0.67    inference(resolution,[],[f239,f26])).
% 0.21/0.67  fof(f26,plain,(
% 0.21/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.67    inference(cnf_transformation,[],[f19])).
% 0.21/0.67  fof(f1353,plain,(
% 0.21/0.67    ( ! [X12,X10,X11] : (sP0(k1_tarski(X12),k2_tarski(X11,X10),k1_enumset1(X10,X11,X12))) )),
% 0.21/0.67    inference(superposition,[],[f129,f1333])).
% 0.21/0.67  fof(f1333,plain,(
% 0.21/0.67    ( ! [X6,X5] : (k2_tarski(X6,X5) = k2_tarski(X5,X6)) )),
% 0.21/0.67    inference(superposition,[],[f1297,f735])).
% 0.21/0.67  fof(f735,plain,(
% 0.21/0.67    ( ! [X4,X3] : (k2_tarski(X4,X3) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X3))) )),
% 0.21/0.67    inference(backward_demodulation,[],[f351,f718])).
% 0.21/0.67  fof(f351,plain,(
% 0.21/0.67    ( ! [X4,X3] : (k2_tarski(X4,X3) = k2_xboole_0(k1_enumset1(X3,X4,X4),k1_tarski(X3))) )),
% 0.21/0.67    inference(resolution,[],[f334,f32])).
% 0.21/0.67  fof(f334,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(k1_tarski(X0),k1_enumset1(X0,X1,X1),k2_tarski(X1,X0))) )),
% 0.21/0.67    inference(superposition,[],[f160,f321])).
% 0.21/0.67  fof(f321,plain,(
% 0.21/0.67    ( ! [X15,X16] : (k2_tarski(X15,X16) = k2_xboole_0(k1_tarski(X16),k2_tarski(X15,X16))) )),
% 0.21/0.67    inference(superposition,[],[f304,f110])).
% 0.21/0.67  fof(f304,plain,(
% 0.21/0.67    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 0.21/0.67    inference(resolution,[],[f302,f32])).
% 0.21/0.67  fof(f302,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(subsumption_resolution,[],[f301,f274])).
% 0.21/0.67  fof(f274,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X0),k2_xboole_0(X2,X1)) | sP0(X0,X1,X0)) )),
% 0.21/0.67    inference(resolution,[],[f243,f36])).
% 0.21/0.67  fof(f243,plain,(
% 0.21/0.67    ( ! [X6,X8,X7,X9] : (~sP0(X7,X9,X8) | r2_hidden(sK4(X6,X7,X6),X8) | sP0(X6,X7,X6)) )),
% 0.21/0.67    inference(resolution,[],[f238,f27])).
% 0.21/0.67  fof(f238,plain,(
% 0.21/0.67    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 0.21/0.67    inference(subsumption_resolution,[],[f230,f30])).
% 0.21/0.67  fof(f230,plain,(
% 0.21/0.67    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X2) | r2_hidden(sK4(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 0.21/0.67    inference(factoring,[],[f28])).
% 0.21/0.67  fof(f301,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(duplicate_literal_removal,[],[f285])).
% 0.21/0.67  fof(f285,plain,(
% 0.21/0.67    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) | sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))) )),
% 0.21/0.67    inference(resolution,[],[f274,f30])).
% 0.21/0.67  fof(f129,plain,(
% 0.21/0.67    ( ! [X2,X0,X1] : (sP0(k1_tarski(X2),k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.67    inference(superposition,[],[f36,f109])).
% 0.21/0.67  fof(f21,plain,(
% 0.21/0.67    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 0.21/0.67    inference(cnf_transformation,[],[f14])).
% 0.21/0.67  fof(f14,plain,(
% 0.21/0.67    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 0.21/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f13])).
% 0.21/0.67  fof(f13,plain,(
% 0.21/0.67    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK1,sK3,sK2)),
% 0.21/0.67    introduced(choice_axiom,[])).
% 0.21/0.67  fof(f10,plain,(
% 0.21/0.67    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 0.21/0.67    inference(ennf_transformation,[],[f9])).
% 0.21/0.67  fof(f9,negated_conjecture,(
% 0.21/0.67    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.67    inference(negated_conjecture,[],[f8])).
% 0.21/0.67  fof(f8,conjecture,(
% 0.21/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 0.21/0.67  % SZS output end Proof for theBenchmark
% 0.21/0.67  % (20416)------------------------------
% 0.21/0.67  % (20416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.67  % (20416)Termination reason: Refutation
% 0.21/0.67  
% 0.21/0.67  % (20416)Memory used [KB]: 7291
% 0.21/0.67  % (20416)Time elapsed: 0.238 s
% 0.21/0.67  % (20416)------------------------------
% 0.21/0.67  % (20416)------------------------------
% 0.21/0.67  % (20405)Success in time 0.301 s
%------------------------------------------------------------------------------
