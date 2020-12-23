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
% DateTime   : Thu Dec  3 12:36:49 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  236 ( 440 expanded)
%              Number of equality atoms :  148 ( 270 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(subsumption_resolution,[],[f351,f45])).

fof(f45,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f351,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f350,f44])).

fof(f44,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f350,plain,
    ( sK1 = sK2
    | sK1 = sK3 ),
    inference(resolution,[],[f345,f276])).

fof(f276,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X9,k2_tarski(X8,X10))
      | X8 = X9
      | X9 = X10 ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X10,X8,X9] :
      ( X8 = X9
      | X8 = X9
      | ~ r2_hidden(X9,k2_tarski(X8,X10))
      | X9 = X10 ) ),
    inference(resolution,[],[f61,f91])).

fof(f91,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f78,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f345,plain,(
    r2_hidden(sK1,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f90,f334])).

fof(f334,plain,(
    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK1) ),
    inference(superposition,[],[f329,f157])).

fof(f157,plain,(
    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f155,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f155,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f52,f153])).

fof(f153,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f152,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f104,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f110,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f110,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f54,f106])).

fof(f106,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f105,f47])).

fof(f105,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f53,f83])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f152,plain,(
    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f53,f87])).

fof(f87,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f329,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f324,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f324,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f323,f51])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f322,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f322,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f292,f59])).

fof(f292,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f291,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f291,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f73,f60])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f90,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f78,f75])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:19:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.27/0.53  % (7704)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (7720)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (7712)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (7712)Refutation not found, incomplete strategy% (7712)------------------------------
% 1.38/0.55  % (7712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (7692)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.56  % (7712)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (7712)Memory used [KB]: 10746
% 1.38/0.56  % (7712)Time elapsed: 0.128 s
% 1.38/0.56  % (7712)------------------------------
% 1.38/0.56  % (7712)------------------------------
% 1.38/0.56  % (7692)Refutation not found, incomplete strategy% (7692)------------------------------
% 1.38/0.56  % (7692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (7692)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (7692)Memory used [KB]: 1663
% 1.38/0.56  % (7692)Time elapsed: 0.150 s
% 1.38/0.56  % (7692)------------------------------
% 1.38/0.56  % (7692)------------------------------
% 1.38/0.56  % (7715)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.56  % (7699)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.57  % (7715)Refutation not found, incomplete strategy% (7715)------------------------------
% 1.38/0.57  % (7715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (7707)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.57  % (7706)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.57  % (7714)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.57  % (7707)Refutation not found, incomplete strategy% (7707)------------------------------
% 1.38/0.57  % (7707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (7707)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (7707)Memory used [KB]: 6268
% 1.38/0.57  % (7707)Time elapsed: 0.166 s
% 1.38/0.57  % (7707)------------------------------
% 1.38/0.57  % (7707)------------------------------
% 1.38/0.57  % (7715)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (7715)Memory used [KB]: 1791
% 1.38/0.57  % (7715)Time elapsed: 0.168 s
% 1.38/0.57  % (7715)------------------------------
% 1.38/0.57  % (7715)------------------------------
% 1.38/0.58  % (7701)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.58  % (7698)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.58  % (7697)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.59  % (7699)Refutation found. Thanks to Tanya!
% 1.38/0.59  % SZS status Theorem for theBenchmark
% 1.38/0.59  % SZS output start Proof for theBenchmark
% 1.38/0.59  fof(f352,plain,(
% 1.38/0.59    $false),
% 1.38/0.59    inference(subsumption_resolution,[],[f351,f45])).
% 1.38/0.59  fof(f45,plain,(
% 1.38/0.59    sK1 != sK3),
% 1.38/0.59    inference(cnf_transformation,[],[f32])).
% 1.38/0.59  fof(f32,plain,(
% 1.38/0.59    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.38/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f31])).
% 1.38/0.59  fof(f31,plain,(
% 1.38/0.59    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f24,plain,(
% 1.38/0.59    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.59    inference(ennf_transformation,[],[f21])).
% 1.38/0.59  fof(f21,negated_conjecture,(
% 1.38/0.59    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.59    inference(negated_conjecture,[],[f20])).
% 1.38/0.59  fof(f20,conjecture,(
% 1.38/0.59    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.38/0.59  fof(f351,plain,(
% 1.38/0.59    sK1 = sK3),
% 1.38/0.59    inference(subsumption_resolution,[],[f350,f44])).
% 1.38/0.59  fof(f44,plain,(
% 1.38/0.59    sK1 != sK2),
% 1.38/0.59    inference(cnf_transformation,[],[f32])).
% 1.38/0.59  fof(f350,plain,(
% 1.38/0.59    sK1 = sK2 | sK1 = sK3),
% 1.38/0.59    inference(resolution,[],[f345,f276])).
% 1.38/0.59  fof(f276,plain,(
% 1.38/0.59    ( ! [X10,X8,X9] : (~r2_hidden(X9,k2_tarski(X8,X10)) | X8 = X9 | X9 = X10) )),
% 1.38/0.59    inference(duplicate_literal_removal,[],[f271])).
% 1.38/0.59  fof(f271,plain,(
% 1.38/0.59    ( ! [X10,X8,X9] : (X8 = X9 | X8 = X9 | ~r2_hidden(X9,k2_tarski(X8,X10)) | X9 = X10) )),
% 1.38/0.59    inference(resolution,[],[f61,f91])).
% 1.38/0.59  fof(f91,plain,(
% 1.38/0.59    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 1.38/0.59    inference(superposition,[],[f78,f51])).
% 1.38/0.59  fof(f51,plain,(
% 1.38/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f14])).
% 1.38/0.59  fof(f14,axiom,(
% 1.38/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.59  fof(f78,plain,(
% 1.38/0.59    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.38/0.59    inference(equality_resolution,[],[f69])).
% 1.38/0.59  fof(f69,plain,(
% 1.38/0.59    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.38/0.59    inference(cnf_transformation,[],[f42])).
% 1.38/0.59  fof(f42,plain,(
% 1.38/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.59    inference(nnf_transformation,[],[f30])).
% 1.38/0.59  fof(f30,plain,(
% 1.38/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.38/0.59    inference(definition_folding,[],[f28,f29])).
% 1.38/0.59  fof(f29,plain,(
% 1.38/0.59    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.38/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.59  fof(f28,plain,(
% 1.38/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.38/0.59    inference(ennf_transformation,[],[f10])).
% 1.38/0.59  fof(f10,axiom,(
% 1.38/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.38/0.59  fof(f61,plain,(
% 1.38/0.59    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.38/0.59    inference(cnf_transformation,[],[f41])).
% 1.38/0.59  fof(f41,plain,(
% 1.38/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.38/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 1.38/0.59  fof(f40,plain,(
% 1.38/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f39,plain,(
% 1.38/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.38/0.59    inference(rectify,[],[f38])).
% 1.38/0.59  fof(f38,plain,(
% 1.38/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.38/0.59    inference(flattening,[],[f37])).
% 1.38/0.59  fof(f37,plain,(
% 1.38/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.38/0.59    inference(nnf_transformation,[],[f29])).
% 1.38/0.59  fof(f345,plain,(
% 1.38/0.59    r2_hidden(sK1,k2_tarski(sK2,sK3))),
% 1.38/0.59    inference(superposition,[],[f90,f334])).
% 1.38/0.59  fof(f334,plain,(
% 1.38/0.59    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK1)),
% 1.38/0.59    inference(superposition,[],[f329,f157])).
% 1.38/0.59  fof(f157,plain,(
% 1.38/0.59    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1))),
% 1.38/0.59    inference(forward_demodulation,[],[f155,f47])).
% 1.38/0.59  fof(f47,plain,(
% 1.38/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.59    inference(cnf_transformation,[],[f7])).
% 1.38/0.59  fof(f7,axiom,(
% 1.38/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.38/0.59  fof(f155,plain,(
% 1.38/0.59    k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0)),
% 1.38/0.59    inference(superposition,[],[f52,f153])).
% 1.38/0.59  fof(f153,plain,(
% 1.38/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.38/0.59    inference(forward_demodulation,[],[f152,f114])).
% 1.38/0.59  fof(f114,plain,(
% 1.38/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.59    inference(backward_demodulation,[],[f104,f113])).
% 1.38/0.59  fof(f113,plain,(
% 1.38/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.38/0.59    inference(forward_demodulation,[],[f110,f83])).
% 1.38/0.59  fof(f83,plain,(
% 1.38/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.59    inference(resolution,[],[f82,f49])).
% 1.38/0.59  fof(f49,plain,(
% 1.38/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.38/0.59    inference(cnf_transformation,[],[f34])).
% 1.38/0.59  fof(f34,plain,(
% 1.38/0.59    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.38/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).
% 1.38/0.59  fof(f33,plain,(
% 1.38/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f25,plain,(
% 1.38/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.38/0.59    inference(ennf_transformation,[],[f3])).
% 1.38/0.59  fof(f3,axiom,(
% 1.38/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.38/0.59  fof(f82,plain,(
% 1.38/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.38/0.59    inference(resolution,[],[f56,f46])).
% 1.38/0.59  fof(f46,plain,(
% 1.38/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f8])).
% 1.38/0.59  fof(f8,axiom,(
% 1.38/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.59  fof(f56,plain,(
% 1.38/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.38/0.59    inference(cnf_transformation,[],[f36])).
% 1.38/0.59  fof(f36,plain,(
% 1.38/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f35])).
% 1.38/0.59  fof(f35,plain,(
% 1.38/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.38/0.59    introduced(choice_axiom,[])).
% 1.38/0.59  fof(f26,plain,(
% 1.38/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.59    inference(ennf_transformation,[],[f23])).
% 1.38/0.59  fof(f23,plain,(
% 1.38/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.59    inference(rectify,[],[f2])).
% 1.38/0.59  fof(f2,axiom,(
% 1.38/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.38/0.59  fof(f110,plain,(
% 1.38/0.59    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.38/0.59    inference(superposition,[],[f54,f106])).
% 1.38/0.59  fof(f106,plain,(
% 1.38/0.59    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.38/0.59    inference(forward_demodulation,[],[f105,f47])).
% 1.38/0.59  fof(f105,plain,(
% 1.38/0.59    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.38/0.59    inference(superposition,[],[f53,f83])).
% 1.38/0.59  fof(f53,plain,(
% 1.38/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.59    inference(cnf_transformation,[],[f4])).
% 1.38/0.59  fof(f4,axiom,(
% 1.38/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.59  fof(f54,plain,(
% 1.38/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.59    inference(cnf_transformation,[],[f6])).
% 1.38/0.59  fof(f6,axiom,(
% 1.38/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.59  fof(f104,plain,(
% 1.38/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.38/0.59    inference(superposition,[],[f53,f50])).
% 1.38/0.59  fof(f50,plain,(
% 1.38/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.38/0.59    inference(cnf_transformation,[],[f22])).
% 1.38/0.59  fof(f22,plain,(
% 1.38/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.38/0.59    inference(rectify,[],[f1])).
% 1.38/0.59  fof(f1,axiom,(
% 1.38/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.38/0.59  fof(f152,plain,(
% 1.38/0.59    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.38/0.59    inference(superposition,[],[f53,f87])).
% 1.38/0.59  fof(f87,plain,(
% 1.38/0.59    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.38/0.59    inference(resolution,[],[f57,f43])).
% 1.38/0.59  fof(f43,plain,(
% 1.38/0.59    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.38/0.59    inference(cnf_transformation,[],[f32])).
% 1.38/0.59  fof(f57,plain,(
% 1.38/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.38/0.59    inference(cnf_transformation,[],[f27])).
% 1.38/0.59  fof(f27,plain,(
% 1.38/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.38/0.59    inference(ennf_transformation,[],[f5])).
% 1.38/0.59  fof(f5,axiom,(
% 1.38/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.38/0.59  fof(f52,plain,(
% 1.38/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.59    inference(cnf_transformation,[],[f9])).
% 1.38/0.59  fof(f9,axiom,(
% 1.38/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.38/0.59  fof(f329,plain,(
% 1.38/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.38/0.59    inference(forward_demodulation,[],[f324,f59])).
% 1.38/0.59  fof(f59,plain,(
% 1.38/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f15])).
% 1.38/0.59  fof(f15,axiom,(
% 1.38/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.59  fof(f324,plain,(
% 1.38/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.38/0.59    inference(superposition,[],[f323,f51])).
% 1.38/0.59  fof(f323,plain,(
% 1.38/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.38/0.59    inference(forward_demodulation,[],[f322,f60])).
% 1.38/0.59  fof(f60,plain,(
% 1.38/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f16])).
% 1.38/0.59  fof(f16,axiom,(
% 1.38/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.38/0.59  fof(f322,plain,(
% 1.38/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.38/0.59    inference(superposition,[],[f292,f59])).
% 1.38/0.59  fof(f292,plain,(
% 1.38/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.38/0.59    inference(forward_demodulation,[],[f291,f71])).
% 1.38/0.59  fof(f71,plain,(
% 1.38/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f17])).
% 1.38/0.59  fof(f17,axiom,(
% 1.38/0.59    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.38/0.59  fof(f291,plain,(
% 1.38/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.38/0.59    inference(superposition,[],[f73,f60])).
% 1.38/0.59  fof(f73,plain,(
% 1.38/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.38/0.59    inference(cnf_transformation,[],[f12])).
% 1.38/0.59  fof(f12,axiom,(
% 1.38/0.59    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 1.38/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 1.38/0.59  fof(f90,plain,(
% 1.38/0.59    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 1.38/0.59    inference(resolution,[],[f78,f75])).
% 1.38/0.59  fof(f75,plain,(
% 1.38/0.59    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.38/0.59    inference(equality_resolution,[],[f64])).
% 1.38/0.59  fof(f64,plain,(
% 1.38/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.38/0.59    inference(cnf_transformation,[],[f41])).
% 1.38/0.59  % SZS output end Proof for theBenchmark
% 1.38/0.59  % (7699)------------------------------
% 1.38/0.59  % (7699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.59  % (7699)Termination reason: Refutation
% 1.38/0.59  
% 1.38/0.59  % (7699)Memory used [KB]: 6524
% 1.38/0.59  % (7699)Time elapsed: 0.174 s
% 1.38/0.59  % (7699)------------------------------
% 1.38/0.59  % (7699)------------------------------
% 1.38/0.59  % (7691)Success in time 0.23 s
%------------------------------------------------------------------------------
