%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 242 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  201 ( 509 expanded)
%              Number of equality atoms :  149 ( 398 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(subsumption_resolution,[],[f376,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f376,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f374,f123])).

fof(f123,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X8,X7] :
      ( X7 = X8
      | X7 = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(resolution,[],[f41,f75])).

fof(f75,plain,(
    ! [X0] : sP0(X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f66,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f374,plain,(
    r2_hidden(sK1,k1_tarski(sK2)) ),
    inference(superposition,[],[f70,f366])).

fof(f366,plain,(
    k1_tarski(sK2) = k2_tarski(sK2,sK1) ),
    inference(superposition,[],[f365,f82])).

fof(f82,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f81,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f81,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0) ),
    inference(superposition,[],[f37,f80])).

fof(f80,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f79,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f79,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f36,f30])).

fof(f30,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f365,plain,(
    ! [X10,X9] : k2_tarski(X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10)) ),
    inference(forward_demodulation,[],[f360,f234])).

fof(f234,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k2_enumset1(X2,X2,X2,X1) ),
    inference(superposition,[],[f224,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f224,plain,(
    ! [X6,X7] : k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7) ),
    inference(superposition,[],[f218,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2) ),
    inference(superposition,[],[f194,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f194,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17) ),
    inference(forward_demodulation,[],[f192,f193])).

fof(f193,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f189,f40])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f188,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f187,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f187,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f186,f40])).

fof(f186,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f185,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f185,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f158,f51])).

fof(f158,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f157,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f157,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f55,f52])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f192,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17)) ),
    inference(superposition,[],[f188,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f39,f38])).

fof(f218,plain,(
    ! [X8,X9] : k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8) ),
    inference(forward_demodulation,[],[f202,f35])).

fof(f202,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9) ),
    inference(superposition,[],[f195,f83])).

fof(f360,plain,(
    ! [X10,X9] : k2_enumset1(X9,X9,X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10)) ),
    inference(superposition,[],[f193,f109])).

fof(f109,plain,(
    ! [X5] : k1_enumset1(X5,X5,X5) = k1_tarski(X5) ),
    inference(resolution,[],[f50,f75])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f65,f35])).

fof(f65,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (23879)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (23860)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (23879)Refutation not found, incomplete strategy% (23879)------------------------------
% 0.21/0.49  % (23879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23879)Memory used [KB]: 10746
% 0.21/0.49  % (23879)Time elapsed: 0.088 s
% 0.21/0.49  % (23879)------------------------------
% 0.21/0.49  % (23879)------------------------------
% 0.21/0.49  % (23863)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (23863)Refutation not found, incomplete strategy% (23863)------------------------------
% 0.21/0.49  % (23863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23863)Memory used [KB]: 6140
% 0.21/0.49  % (23863)Time elapsed: 0.080 s
% 0.21/0.49  % (23863)------------------------------
% 0.21/0.49  % (23863)------------------------------
% 0.21/0.49  % (23868)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (23869)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (23888)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (23869)Refutation not found, incomplete strategy% (23869)------------------------------
% 0.21/0.50  % (23869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23869)Memory used [KB]: 10618
% 0.21/0.50  % (23869)Time elapsed: 0.099 s
% 0.21/0.50  % (23869)------------------------------
% 0.21/0.50  % (23869)------------------------------
% 0.21/0.50  % (23868)Refutation not found, incomplete strategy% (23868)------------------------------
% 0.21/0.50  % (23868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23876)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (23868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23868)Memory used [KB]: 10618
% 0.21/0.50  % (23868)Time elapsed: 0.102 s
% 0.21/0.50  % (23868)------------------------------
% 0.21/0.50  % (23868)------------------------------
% 0.21/0.50  % (23876)Refutation not found, incomplete strategy% (23876)------------------------------
% 0.21/0.50  % (23876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23876)Memory used [KB]: 10618
% 0.21/0.50  % (23876)Time elapsed: 0.096 s
% 0.21/0.50  % (23876)------------------------------
% 0.21/0.50  % (23876)------------------------------
% 0.21/0.50  % (23881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (23874)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (23864)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (23861)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23877)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (23866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (23859)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (23872)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (23883)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (23880)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (23880)Refutation not found, incomplete strategy% (23880)------------------------------
% 0.21/0.51  % (23880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23861)Refutation not found, incomplete strategy% (23861)------------------------------
% 0.21/0.51  % (23861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23861)Memory used [KB]: 10618
% 0.21/0.51  % (23861)Time elapsed: 0.109 s
% 0.21/0.51  % (23861)------------------------------
% 0.21/0.51  % (23861)------------------------------
% 0.21/0.51  % (23865)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (23875)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (23862)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (23880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23880)Memory used [KB]: 1663
% 0.21/0.52  % (23880)Time elapsed: 0.089 s
% 0.21/0.52  % (23880)------------------------------
% 0.21/0.52  % (23880)------------------------------
% 0.21/0.52  % (23887)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (23882)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (23882)Refutation not found, incomplete strategy% (23882)------------------------------
% 0.21/0.52  % (23882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23882)Memory used [KB]: 1663
% 0.21/0.52  % (23882)Time elapsed: 0.109 s
% 0.21/0.52  % (23882)------------------------------
% 0.21/0.52  % (23882)------------------------------
% 0.21/0.52  % (23859)Refutation not found, incomplete strategy% (23859)------------------------------
% 0.21/0.52  % (23859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23859)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23859)Memory used [KB]: 1663
% 0.21/0.52  % (23859)Time elapsed: 0.119 s
% 0.21/0.52  % (23859)------------------------------
% 0.21/0.52  % (23859)------------------------------
% 0.21/0.52  % (23886)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (23871)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23884)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (23867)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (23884)Refutation not found, incomplete strategy% (23884)------------------------------
% 0.21/0.52  % (23884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23884)Memory used [KB]: 6268
% 0.21/0.52  % (23884)Time elapsed: 0.123 s
% 0.21/0.52  % (23884)------------------------------
% 0.21/0.52  % (23884)------------------------------
% 0.21/0.52  % (23881)Refutation not found, incomplete strategy% (23881)------------------------------
% 0.21/0.52  % (23881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23881)Memory used [KB]: 10746
% 0.21/0.52  % (23881)Time elapsed: 0.125 s
% 0.21/0.52  % (23881)------------------------------
% 0.21/0.52  % (23881)------------------------------
% 0.21/0.52  % (23867)Refutation not found, incomplete strategy% (23867)------------------------------
% 0.21/0.52  % (23867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23874)Refutation not found, incomplete strategy% (23874)------------------------------
% 0.21/0.53  % (23874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23874)Memory used [KB]: 6140
% 0.21/0.53  % (23874)Time elapsed: 0.107 s
% 0.21/0.53  % (23874)------------------------------
% 0.21/0.53  % (23874)------------------------------
% 0.21/0.53  % (23878)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (23873)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (23870)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (23866)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (23885)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (23867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23867)Memory used [KB]: 10618
% 0.21/0.53  % (23867)Time elapsed: 0.128 s
% 0.21/0.53  % (23867)------------------------------
% 0.21/0.53  % (23867)------------------------------
% 0.21/0.53  % (23885)Refutation not found, incomplete strategy% (23885)------------------------------
% 0.21/0.53  % (23885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23885)Memory used [KB]: 10746
% 0.21/0.54  % (23885)Time elapsed: 0.133 s
% 0.21/0.54  % (23885)------------------------------
% 0.21/0.54  % (23885)------------------------------
% 0.21/0.54  % (23870)Refutation not found, incomplete strategy% (23870)------------------------------
% 0.21/0.54  % (23870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23870)Memory used [KB]: 10618
% 0.21/0.54  % (23870)Time elapsed: 0.138 s
% 0.21/0.54  % (23870)------------------------------
% 0.21/0.54  % (23870)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f376,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    sK1 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.21/0.54  fof(f376,plain,(
% 0.21/0.54    sK1 = sK2),
% 0.21/0.54    inference(resolution,[],[f374,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X8,X7] : (~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X8,X7] : (X7 = X8 | X7 = X8 | ~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.21/0.54    inference(resolution,[],[f41,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0] : (sP0(X0,X0,X0,k1_tarski(X0))) )),
% 0.21/0.54    inference(superposition,[],[f66,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(superposition,[],[f59,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.21/0.54    inference(definition_folding,[],[f19,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.54    inference(rectify,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_tarski(sK2))),
% 0.21/0.54    inference(superposition,[],[f70,f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    k1_tarski(sK2) = k2_tarski(sK2,sK1)),
% 0.21/0.54    inference(superposition,[],[f365,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 0.21/0.54    inference(forward_demodulation,[],[f81,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f37,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f79,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.21/0.54    inference(superposition,[],[f36,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    ( ! [X10,X9] : (k2_tarski(X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f360,f234])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k2_tarski(X2,X1) = k2_enumset1(X2,X2,X2,X1)) )),
% 0.21/0.54    inference(superposition,[],[f224,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X6,X7] : (k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7)) )),
% 0.21/0.54    inference(superposition,[],[f218,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2)) )),
% 0.21/0.54    inference(superposition,[],[f194,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f192,f193])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f189,f40])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.54    inference(superposition,[],[f188,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f187,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.54    inference(superposition,[],[f186,f40])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f185,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.54    inference(superposition,[],[f158,f51])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f157,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.54    inference(superposition,[],[f55,f52])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17))) )),
% 0.21/0.54    inference(superposition,[],[f188,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f39,f38])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ( ! [X8,X9] : (k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f202,f35])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9)) )),
% 0.21/0.54    inference(superposition,[],[f195,f83])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    ( ! [X10,X9] : (k2_enumset1(X9,X9,X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10))) )),
% 0.21/0.54    inference(superposition,[],[f193,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X5] : (k1_enumset1(X5,X5,X5) = k1_tarski(X5)) )),
% 0.21/0.54    inference(resolution,[],[f50,f75])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) = X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(superposition,[],[f65,f35])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 0.21/0.54    inference(resolution,[],[f59,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.54    inference(equality_resolution,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23866)------------------------------
% 0.21/0.54  % (23866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23866)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23866)Memory used [KB]: 6524
% 0.21/0.54  % (23866)Time elapsed: 0.110 s
% 0.21/0.54  % (23866)------------------------------
% 0.21/0.54  % (23866)------------------------------
% 0.21/0.54  % (23858)Success in time 0.165 s
%------------------------------------------------------------------------------
