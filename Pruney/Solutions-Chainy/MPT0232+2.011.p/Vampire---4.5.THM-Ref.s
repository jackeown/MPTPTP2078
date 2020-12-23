%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:01 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 504 expanded)
%              Number of leaves         :   22 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  241 ( 955 expanded)
%              Number of equality atoms :  178 ( 774 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3770,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3769])).

fof(f3769,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f3750,f3767])).

fof(f3767,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f3726,f3727])).

fof(f3727,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f3656,f106])).

fof(f106,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f3656,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
      | sK2 = X8 ) ),
    inference(superposition,[],[f100,f3579])).

fof(f3579,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f1616,f141])).

fof(f141,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f128,f112])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f68,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f128,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f67,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1616,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f1580,f68])).

fof(f1580,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f603,f117])).

fof(f117,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f44,f82])).

fof(f82,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f39,f78,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f603,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(superposition,[],[f80,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f46,f73,f56,f79])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f100,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f3726,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f3656,f104])).

fof(f104,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3750,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f81,f3726])).

fof(f81,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f40,f78,f79])).

fof(f40,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:12:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.53  % (16683)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (16683)Refutation not found, incomplete strategy% (16683)------------------------------
% 0.19/0.53  % (16683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (16683)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (16683)Memory used [KB]: 10618
% 0.19/0.53  % (16683)Time elapsed: 0.113 s
% 0.19/0.53  % (16683)------------------------------
% 0.19/0.53  % (16683)------------------------------
% 0.19/0.53  % (16699)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.53  % (16693)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.53  % (16696)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (16700)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (16700)Refutation not found, incomplete strategy% (16700)------------------------------
% 0.19/0.53  % (16700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (16700)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (16700)Memory used [KB]: 1663
% 0.19/0.53  % (16700)Time elapsed: 0.133 s
% 0.19/0.53  % (16700)------------------------------
% 0.19/0.53  % (16700)------------------------------
% 0.19/0.54  % (16684)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.54  % (16675)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.54  % (16672)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.54  % (16682)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.54  % (16686)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.54  % (16672)Refutation not found, incomplete strategy% (16672)------------------------------
% 0.19/0.54  % (16672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (16672)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (16672)Memory used [KB]: 1663
% 0.19/0.54  % (16672)Time elapsed: 0.109 s
% 0.19/0.54  % (16672)------------------------------
% 0.19/0.54  % (16672)------------------------------
% 0.19/0.54  % (16691)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (16671)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.54  % (16685)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.55  % (16688)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.55  % (16674)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.55  % (16698)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.55  % (16676)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.55  % (16680)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.55  % (16690)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.55  % (16677)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.55  % (16673)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.55  % (16682)Refutation not found, incomplete strategy% (16682)------------------------------
% 0.19/0.55  % (16682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (16682)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (16682)Memory used [KB]: 6268
% 0.19/0.55  % (16682)Time elapsed: 0.149 s
% 0.19/0.55  % (16682)------------------------------
% 0.19/0.55  % (16682)------------------------------
% 0.19/0.55  % (16697)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.56  % (16696)Refutation not found, incomplete strategy% (16696)------------------------------
% 0.19/0.56  % (16696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (16696)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (16696)Memory used [KB]: 6268
% 0.19/0.56  % (16696)Time elapsed: 0.147 s
% 0.19/0.56  % (16696)------------------------------
% 0.19/0.56  % (16696)------------------------------
% 0.19/0.56  % (16681)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.56  % (16678)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.56  % (16692)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.56  % (16688)Refutation not found, incomplete strategy% (16688)------------------------------
% 0.19/0.56  % (16688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (16688)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (16688)Memory used [KB]: 1791
% 0.19/0.56  % (16688)Time elapsed: 0.137 s
% 0.19/0.56  % (16688)------------------------------
% 0.19/0.56  % (16688)------------------------------
% 0.19/0.56  % (16679)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.56  % (16689)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.56  % (16694)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.57  % (16687)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.57  % (16687)Refutation not found, incomplete strategy% (16687)------------------------------
% 0.19/0.57  % (16687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (16687)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (16687)Memory used [KB]: 10618
% 0.19/0.57  % (16687)Time elapsed: 0.171 s
% 0.19/0.57  % (16687)------------------------------
% 0.19/0.57  % (16687)------------------------------
% 0.19/0.57  % (16698)Refutation not found, incomplete strategy% (16698)------------------------------
% 0.19/0.57  % (16698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (16698)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (16698)Memory used [KB]: 6268
% 0.19/0.57  % (16698)Time elapsed: 0.172 s
% 0.19/0.57  % (16698)------------------------------
% 0.19/0.57  % (16698)------------------------------
% 0.19/0.57  % (16695)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.57  % (16695)Refutation not found, incomplete strategy% (16695)------------------------------
% 0.19/0.57  % (16695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (16695)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.57  
% 0.19/0.57  % (16695)Memory used [KB]: 10746
% 0.19/0.57  % (16695)Time elapsed: 0.171 s
% 0.19/0.57  % (16695)------------------------------
% 0.19/0.57  % (16695)------------------------------
% 0.19/0.58  % (16697)Refutation not found, incomplete strategy% (16697)------------------------------
% 0.19/0.58  % (16697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (16697)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.58  
% 0.19/0.58  % (16697)Memory used [KB]: 6268
% 0.19/0.58  % (16697)Time elapsed: 0.172 s
% 0.19/0.58  % (16697)------------------------------
% 0.19/0.58  % (16697)------------------------------
% 2.07/0.66  % (16738)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.07/0.66  % (16722)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.07/0.68  % (16674)Refutation not found, incomplete strategy% (16674)------------------------------
% 2.07/0.68  % (16674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.68  % (16674)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.68  
% 2.07/0.68  % (16674)Memory used [KB]: 6140
% 2.07/0.68  % (16674)Time elapsed: 0.249 s
% 2.07/0.68  % (16674)------------------------------
% 2.07/0.68  % (16674)------------------------------
% 2.07/0.68  % (16671)Refutation not found, incomplete strategy% (16671)------------------------------
% 2.07/0.68  % (16671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.68  % (16671)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.68  
% 2.07/0.68  % (16671)Memory used [KB]: 1663
% 2.07/0.68  % (16671)Time elapsed: 0.244 s
% 2.07/0.68  % (16671)------------------------------
% 2.07/0.68  % (16671)------------------------------
% 2.07/0.68  % (16742)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.07/0.68  % (16686)Refutation not found, incomplete strategy% (16686)------------------------------
% 2.07/0.68  % (16686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.68  % (16686)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.68  
% 2.07/0.68  % (16686)Memory used [KB]: 6140
% 2.07/0.68  % (16686)Time elapsed: 0.229 s
% 2.07/0.68  % (16686)------------------------------
% 2.07/0.68  % (16686)------------------------------
% 2.07/0.69  % (16733)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.07/0.69  % (16733)Refutation not found, incomplete strategy% (16733)------------------------------
% 2.07/0.69  % (16733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.69  % (16733)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.69  
% 2.07/0.69  % (16733)Memory used [KB]: 6140
% 2.07/0.69  % (16733)Time elapsed: 0.093 s
% 2.07/0.69  % (16733)------------------------------
% 2.07/0.69  % (16733)------------------------------
% 2.07/0.69  % (16748)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.07/0.69  % (16728)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.70/0.70  % (16747)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.70/0.71  % (16749)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.70/0.71  % (16739)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.70/0.71  % (16752)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.70/0.71  % (16739)Refutation not found, incomplete strategy% (16739)------------------------------
% 2.70/0.71  % (16739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.71  % (16739)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.71  
% 2.70/0.71  % (16739)Memory used [KB]: 10746
% 2.70/0.71  % (16739)Time elapsed: 0.120 s
% 2.70/0.71  % (16739)------------------------------
% 2.70/0.71  % (16739)------------------------------
% 2.70/0.73  % (16673)Refutation not found, incomplete strategy% (16673)------------------------------
% 2.70/0.73  % (16673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (16747)Refutation not found, incomplete strategy% (16747)------------------------------
% 2.70/0.73  % (16747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (16747)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.73  
% 2.70/0.73  % (16747)Memory used [KB]: 10746
% 2.70/0.73  % (16747)Time elapsed: 0.117 s
% 2.70/0.73  % (16747)------------------------------
% 2.70/0.73  % (16747)------------------------------
% 2.70/0.74  % (16673)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.74  
% 2.70/0.74  % (16673)Memory used [KB]: 6524
% 2.70/0.74  % (16673)Time elapsed: 0.322 s
% 2.70/0.74  % (16673)------------------------------
% 2.70/0.74  % (16673)------------------------------
% 3.18/0.79  % (16811)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.18/0.81  % (16816)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.18/0.82  % (16821)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.18/0.83  % (16833)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.18/0.85  % (16837)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.18/0.86  % (16854)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.18/0.86  % (16847)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.88/0.91  % (16685)Time limit reached!
% 3.88/0.91  % (16685)------------------------------
% 3.88/0.91  % (16685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.92  % (16685)Termination reason: Time limit
% 4.06/0.92  
% 4.06/0.92  % (16685)Memory used [KB]: 4989
% 4.06/0.92  % (16685)Time elapsed: 0.507 s
% 4.06/0.92  % (16685)------------------------------
% 4.06/0.92  % (16685)------------------------------
% 4.12/0.93  % (16677)Time limit reached!
% 4.12/0.93  % (16677)------------------------------
% 4.12/0.93  % (16677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.93  % (16677)Termination reason: Time limit
% 4.12/0.93  
% 4.12/0.93  % (16677)Memory used [KB]: 15607
% 4.12/0.93  % (16677)Time elapsed: 0.521 s
% 4.12/0.93  % (16677)------------------------------
% 4.12/0.93  % (16677)------------------------------
% 4.55/1.00  % (16847)Refutation not found, incomplete strategy% (16847)------------------------------
% 4.55/1.00  % (16847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.01  % (16847)Termination reason: Refutation not found, incomplete strategy
% 4.55/1.01  
% 4.55/1.01  % (16847)Memory used [KB]: 6140
% 4.55/1.01  % (16847)Time elapsed: 0.249 s
% 4.55/1.01  % (16847)------------------------------
% 4.55/1.01  % (16847)------------------------------
% 4.55/1.03  % (16678)Time limit reached!
% 4.55/1.03  % (16678)------------------------------
% 4.55/1.03  % (16678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.03  % (16678)Termination reason: Time limit
% 4.55/1.03  
% 4.55/1.03  % (16678)Memory used [KB]: 7036
% 4.55/1.03  % (16678)Time elapsed: 0.606 s
% 4.55/1.03  % (16678)------------------------------
% 4.55/1.03  % (16678)------------------------------
% 4.55/1.05  % (16904)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 4.55/1.06  % (16908)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 5.02/1.10  % (16676)Refutation found. Thanks to Tanya!
% 5.02/1.10  % SZS status Theorem for theBenchmark
% 5.02/1.10  % SZS output start Proof for theBenchmark
% 5.02/1.10  fof(f3770,plain,(
% 5.02/1.10    $false),
% 5.02/1.10    inference(trivial_inequality_removal,[],[f3769])).
% 5.02/1.10  fof(f3769,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 5.02/1.10    inference(forward_demodulation,[],[f3750,f3767])).
% 5.02/1.10  fof(f3767,plain,(
% 5.02/1.10    sK0 = sK1),
% 5.02/1.10    inference(backward_demodulation,[],[f3726,f3727])).
% 5.02/1.10  fof(f3727,plain,(
% 5.02/1.10    sK0 = sK2),
% 5.02/1.10    inference(resolution,[],[f3656,f106])).
% 5.02/1.10  fof(f106,plain,(
% 5.02/1.10    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 5.02/1.10    inference(equality_resolution,[],[f105])).
% 5.02/1.10  fof(f105,plain,(
% 5.02/1.10    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 5.02/1.10    inference(equality_resolution,[],[f94])).
% 5.02/1.10  fof(f94,plain,(
% 5.02/1.10    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 5.02/1.10    inference(definition_unfolding,[],[f59,f77])).
% 5.02/1.10  fof(f77,plain,(
% 5.02/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f66,f76])).
% 5.02/1.10  fof(f76,plain,(
% 5.02/1.10    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f72,f75])).
% 5.02/1.10  fof(f75,plain,(
% 5.02/1.10    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f71,f74])).
% 5.02/1.10  fof(f74,plain,(
% 5.02/1.10    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f57,f56])).
% 5.02/1.10  fof(f56,plain,(
% 5.02/1.10    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f19])).
% 5.02/1.10  fof(f19,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 5.02/1.10  fof(f57,plain,(
% 5.02/1.10    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f18])).
% 5.02/1.10  fof(f18,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 5.02/1.10  fof(f71,plain,(
% 5.02/1.10    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f17])).
% 5.02/1.10  fof(f17,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 5.02/1.10  fof(f72,plain,(
% 5.02/1.10    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f16])).
% 5.02/1.10  fof(f16,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 5.02/1.10  fof(f66,plain,(
% 5.02/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f15])).
% 5.02/1.10  fof(f15,axiom,(
% 5.02/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.02/1.10  fof(f59,plain,(
% 5.02/1.10    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.02/1.10    inference(cnf_transformation,[],[f38])).
% 5.02/1.10  fof(f38,plain,(
% 5.02/1.10    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.02/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 5.02/1.10  fof(f37,plain,(
% 5.02/1.10    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 5.02/1.10    introduced(choice_axiom,[])).
% 5.02/1.10  fof(f36,plain,(
% 5.02/1.10    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.02/1.10    inference(rectify,[],[f35])).
% 5.02/1.10  fof(f35,plain,(
% 5.02/1.10    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.02/1.10    inference(flattening,[],[f34])).
% 5.02/1.10  fof(f34,plain,(
% 5.02/1.10    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 5.02/1.10    inference(nnf_transformation,[],[f25])).
% 5.02/1.10  fof(f25,plain,(
% 5.02/1.10    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 5.02/1.10    inference(ennf_transformation,[],[f10])).
% 5.02/1.10  fof(f10,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 5.02/1.10  fof(f3656,plain,(
% 5.02/1.10    ( ! [X8] : (~r2_hidden(X8,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | sK2 = X8) )),
% 5.02/1.10    inference(superposition,[],[f100,f3579])).
% 5.02/1.10  fof(f3579,plain,(
% 5.02/1.10    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 5.02/1.10    inference(superposition,[],[f1616,f141])).
% 5.02/1.10  fof(f141,plain,(
% 5.02/1.10    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 5.02/1.10    inference(forward_demodulation,[],[f128,f112])).
% 5.02/1.10  fof(f112,plain,(
% 5.02/1.10    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.02/1.10    inference(superposition,[],[f68,f69])).
% 5.02/1.10  fof(f69,plain,(
% 5.02/1.10    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.02/1.10    inference(cnf_transformation,[],[f6])).
% 5.02/1.10  fof(f6,axiom,(
% 5.02/1.10    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.02/1.10  fof(f68,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f2])).
% 5.02/1.10  fof(f2,axiom,(
% 5.02/1.10    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.02/1.10  fof(f128,plain,(
% 5.02/1.10    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 5.02/1.10    inference(superposition,[],[f67,f70])).
% 5.02/1.10  fof(f70,plain,(
% 5.02/1.10    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f8])).
% 5.02/1.10  fof(f8,axiom,(
% 5.02/1.10    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.02/1.10  fof(f67,plain,(
% 5.02/1.10    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.02/1.10    inference(cnf_transformation,[],[f7])).
% 5.02/1.10  fof(f7,axiom,(
% 5.02/1.10    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.02/1.10  fof(f1616,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 5.02/1.10    inference(forward_demodulation,[],[f1580,f68])).
% 5.02/1.10  fof(f1580,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 5.02/1.10    inference(superposition,[],[f603,f117])).
% 5.02/1.10  fof(f117,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 5.02/1.10    inference(resolution,[],[f44,f82])).
% 5.02/1.10  fof(f82,plain,(
% 5.02/1.10    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 5.02/1.10    inference(definition_unfolding,[],[f39,f78,f79])).
% 5.02/1.10  fof(f79,plain,(
% 5.02/1.10    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f51,f78])).
% 5.02/1.10  fof(f51,plain,(
% 5.02/1.10    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f13])).
% 5.02/1.10  fof(f13,axiom,(
% 5.02/1.10    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.02/1.10  fof(f78,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 5.02/1.10    inference(definition_unfolding,[],[f52,f77])).
% 5.02/1.10  fof(f52,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f14])).
% 5.02/1.10  fof(f14,axiom,(
% 5.02/1.10    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.02/1.10  fof(f39,plain,(
% 5.02/1.10    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 5.02/1.10    inference(cnf_transformation,[],[f27])).
% 5.02/1.10  fof(f27,plain,(
% 5.02/1.10    k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 5.02/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 5.02/1.10  fof(f26,plain,(
% 5.02/1.10    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 5.02/1.10    introduced(choice_axiom,[])).
% 5.02/1.10  fof(f23,plain,(
% 5.02/1.10    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 5.02/1.10    inference(ennf_transformation,[],[f22])).
% 5.02/1.10  fof(f22,negated_conjecture,(
% 5.02/1.10    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 5.02/1.10    inference(negated_conjecture,[],[f21])).
% 5.02/1.10  fof(f21,conjecture,(
% 5.02/1.10    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 5.02/1.10  fof(f44,plain,(
% 5.02/1.10    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 5.02/1.10    inference(cnf_transformation,[],[f24])).
% 5.02/1.10  fof(f24,plain,(
% 5.02/1.10    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.02/1.10    inference(ennf_transformation,[],[f5])).
% 5.02/1.10  fof(f5,axiom,(
% 5.02/1.10    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.02/1.10  fof(f603,plain,(
% 5.02/1.10    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 5.02/1.10    inference(superposition,[],[f80,f54])).
% 5.02/1.10  fof(f54,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.02/1.10    inference(cnf_transformation,[],[f1])).
% 5.02/1.10  fof(f1,axiom,(
% 5.02/1.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.02/1.10  fof(f80,plain,(
% 5.02/1.10    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 5.02/1.10    inference(definition_unfolding,[],[f46,f73,f56,f79])).
% 5.02/1.10  fof(f73,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.02/1.10    inference(definition_unfolding,[],[f55,f53])).
% 5.02/1.10  fof(f53,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.02/1.10    inference(cnf_transformation,[],[f4])).
% 5.02/1.10  fof(f4,axiom,(
% 5.02/1.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.02/1.10  fof(f55,plain,(
% 5.02/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.02/1.10    inference(cnf_transformation,[],[f9])).
% 5.02/1.10  fof(f9,axiom,(
% 5.02/1.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.02/1.10  fof(f46,plain,(
% 5.02/1.10    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 5.02/1.10    inference(cnf_transformation,[],[f12])).
% 5.02/1.10  fof(f12,axiom,(
% 5.02/1.10    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 5.02/1.10  fof(f100,plain,(
% 5.02/1.10    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 5.02/1.10    inference(equality_resolution,[],[f87])).
% 5.02/1.10  fof(f87,plain,(
% 5.02/1.10    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 5.02/1.10    inference(definition_unfolding,[],[f47,f79])).
% 5.02/1.10  fof(f47,plain,(
% 5.02/1.10    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 5.02/1.10    inference(cnf_transformation,[],[f33])).
% 5.02/1.10  fof(f33,plain,(
% 5.02/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 5.02/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 5.02/1.10  fof(f32,plain,(
% 5.02/1.10    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 5.02/1.10    introduced(choice_axiom,[])).
% 5.02/1.10  fof(f31,plain,(
% 5.02/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 5.02/1.10    inference(rectify,[],[f30])).
% 5.02/1.10  fof(f30,plain,(
% 5.02/1.10    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 5.02/1.10    inference(nnf_transformation,[],[f11])).
% 5.02/1.10  fof(f11,axiom,(
% 5.02/1.10    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 5.02/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 5.02/1.10  fof(f3726,plain,(
% 5.02/1.10    sK1 = sK2),
% 5.02/1.10    inference(resolution,[],[f3656,f104])).
% 5.02/1.10  fof(f104,plain,(
% 5.02/1.10    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 5.02/1.10    inference(equality_resolution,[],[f103])).
% 5.02/1.10  fof(f103,plain,(
% 5.02/1.10    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 5.02/1.10    inference(equality_resolution,[],[f93])).
% 5.02/1.10  fof(f93,plain,(
% 5.02/1.10    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 5.02/1.10    inference(definition_unfolding,[],[f60,f77])).
% 5.02/1.10  fof(f60,plain,(
% 5.02/1.10    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 5.02/1.10    inference(cnf_transformation,[],[f38])).
% 5.02/1.10  fof(f3750,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 5.02/1.10    inference(backward_demodulation,[],[f81,f3726])).
% 5.02/1.10  fof(f81,plain,(
% 5.02/1.10    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 5.02/1.10    inference(definition_unfolding,[],[f40,f78,f79])).
% 5.02/1.10  fof(f40,plain,(
% 5.02/1.10    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 5.02/1.10    inference(cnf_transformation,[],[f27])).
% 5.02/1.10  % SZS output end Proof for theBenchmark
% 5.02/1.10  % (16676)------------------------------
% 5.02/1.10  % (16676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.10  % (16676)Termination reason: Refutation
% 5.02/1.10  
% 5.02/1.10  % (16676)Memory used [KB]: 4989
% 5.02/1.10  % (16676)Time elapsed: 0.675 s
% 5.02/1.10  % (16676)------------------------------
% 5.02/1.10  % (16676)------------------------------
% 5.02/1.10  % (16670)Success in time 0.754 s
%------------------------------------------------------------------------------
