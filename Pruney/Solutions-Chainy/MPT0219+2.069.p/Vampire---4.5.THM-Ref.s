%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 (47568 expanded)
%              Number of leaves         :   18 (16476 expanded)
%              Depth                    :   46
%              Number of atoms          :  242 (50344 expanded)
%              Number of equality atoms :  211 (50291 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f715,plain,(
    $false ),
    inference(subsumption_resolution,[],[f714,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f714,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f713])).

fof(f713,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f709,f75])).

fof(f75,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f709,plain,(
    r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f70,f652])).

fof(f652,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f651,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f651,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f620,f103])).

fof(f103,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f94,f96])).

fof(f96,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f92,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f92,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(forward_demodulation,[],[f89,f88])).

fof(f88,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f57,f84])).

fof(f84,plain,(
    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f83,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f80,f29])).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f32,f35,f51])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) ),
    inference(forward_demodulation,[],[f77,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[],[f38,f76])).

fof(f76,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f58,f31])).

fof(f58,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f27,f56,f51,f56,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f50,f51,f49,f56])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f89,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f60,f84])).

fof(f94,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f93,f31])).

fof(f93,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))) ),
    inference(forward_demodulation,[],[f90,f88])).

fof(f90,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f59,f84])).

fof(f620,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f57,f568])).

fof(f568,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f380,f567])).

fof(f567,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f565,f479])).

fof(f479,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f464,f29])).

fof(f464,plain,(
    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f341,f331])).

fof(f331,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f330,f329])).

fof(f329,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    inference(forward_demodulation,[],[f323,f31])).

fof(f323,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f60,f95])).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(forward_demodulation,[],[f91,f38])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) ),
    inference(superposition,[],[f38,f84])).

fof(f330,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) ),
    inference(forward_demodulation,[],[f324,f31])).

fof(f324,plain,(
    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ),
    inference(superposition,[],[f59,f95])).

fof(f341,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f38,f331])).

fof(f565,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f110,f398])).

fof(f398,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f390,f29])).

fof(f390,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f282,f103])).

fof(f282,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(backward_demodulation,[],[f237,f269])).

fof(f269,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1) = k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,X1) ),
    inference(backward_demodulation,[],[f220,f268])).

fof(f268,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,X1) ),
    inference(forward_demodulation,[],[f266,f57])).

fof(f266,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f57,f223])).

fof(f223,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f176,f221])).

fof(f221,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1) ),
    inference(backward_demodulation,[],[f174,f220])).

fof(f174,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1) ),
    inference(forward_demodulation,[],[f172,f57])).

fof(f172,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)))) ),
    inference(superposition,[],[f57,f142])).

fof(f142,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f111,f141])).

fof(f141,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,X1) ),
    inference(forward_demodulation,[],[f139,f57])).

fof(f139,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1)))) ),
    inference(superposition,[],[f57,f111])).

fof(f111,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) ),
    inference(superposition,[],[f104,f29])).

fof(f104,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f103])).

fof(f98,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f57,f92])).

fof(f176,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f142,f175])).

fof(f175,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,X1) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1) ),
    inference(backward_demodulation,[],[f141,f174])).

fof(f220,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1) ),
    inference(forward_demodulation,[],[f218,f57])).

fof(f218,plain,(
    ! [X1] : k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f57,f176])).

fof(f237,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),X0) ),
    inference(backward_demodulation,[],[f213,f221])).

fof(f213,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f212,f38])).

fof(f212,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
    inference(superposition,[],[f38,f180])).

fof(f180,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f146,f175])).

fof(f146,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f119,f141])).

fof(f119,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) ),
    inference(backward_demodulation,[],[f88,f111])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f38,f103])).

fof(f380,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f60,f274])).

fof(f274,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f225,f269])).

fof(f225,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f178,f221])).

fof(f178,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f144,f175])).

fof(f144,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f117,f141])).

fof(f117,plain,(
    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f96,f111])).

fof(f70,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:44:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (25023)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.49  % (25030)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (25041)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (25018)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (25033)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (25036)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (25025)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (25033)Refutation not found, incomplete strategy% (25033)------------------------------
% 0.20/0.50  % (25033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25033)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25033)Memory used [KB]: 6140
% 0.20/0.50  % (25033)Time elapsed: 0.056 s
% 0.20/0.50  % (25033)------------------------------
% 0.20/0.50  % (25033)------------------------------
% 0.20/0.50  % (25026)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (25039)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (25018)Refutation not found, incomplete strategy% (25018)------------------------------
% 0.20/0.50  % (25018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25018)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25018)Memory used [KB]: 1663
% 0.20/0.50  % (25018)Time elapsed: 0.103 s
% 0.20/0.50  % (25018)------------------------------
% 0.20/0.50  % (25018)------------------------------
% 0.20/0.50  % (25047)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (25022)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (25021)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (25024)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (25042)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (25038)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (25034)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (25043)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (25037)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (25045)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (25032)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (25029)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (25029)Refutation not found, incomplete strategy% (25029)------------------------------
% 0.20/0.54  % (25029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25029)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25029)Memory used [KB]: 10618
% 0.20/0.54  % (25029)Time elapsed: 0.151 s
% 0.20/0.54  % (25029)------------------------------
% 0.20/0.54  % (25029)------------------------------
% 0.20/0.54  % (25031)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (25028)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (25028)Refutation not found, incomplete strategy% (25028)------------------------------
% 0.20/0.54  % (25028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25020)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (25028)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25028)Memory used [KB]: 10618
% 0.20/0.55  % (25028)Time elapsed: 0.147 s
% 0.20/0.55  % (25028)------------------------------
% 0.20/0.55  % (25028)------------------------------
% 0.20/0.55  % (25046)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (25035)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (25027)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (25035)Refutation not found, incomplete strategy% (25035)------------------------------
% 0.20/0.57  % (25035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (25019)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.57  % (25035)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (25035)Memory used [KB]: 10618
% 0.20/0.57  % (25035)Time elapsed: 0.173 s
% 0.20/0.57  % (25035)------------------------------
% 0.20/0.57  % (25035)------------------------------
% 0.20/0.57  % (25026)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (25044)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f715,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(subsumption_resolution,[],[f714,f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    sK0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.58    inference(negated_conjecture,[],[f16])).
% 0.20/0.58  fof(f16,conjecture,(
% 0.20/0.58    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.20/0.58  fof(f714,plain,(
% 0.20/0.58    sK0 = sK1),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f713])).
% 0.20/0.58  fof(f713,plain,(
% 0.20/0.58    sK0 = sK1 | sK0 = sK1 | sK0 = sK1),
% 0.20/0.58    inference(resolution,[],[f709,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.20/0.58    inference(equality_resolution,[],[f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.58    inference(definition_unfolding,[],[f40,f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f37,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f39,f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f48,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.58    inference(rectify,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.58    inference(flattening,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.58    inference(nnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.58  fof(f709,plain,(
% 0.20/0.58    r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(superposition,[],[f70,f652])).
% 0.20/0.58  fof(f652,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.58    inference(forward_demodulation,[],[f651,f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.58  fof(f651,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.20/0.58    inference(forward_demodulation,[],[f620,f103])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.58    inference(backward_demodulation,[],[f94,f96])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.58    inference(superposition,[],[f92,f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f89,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.58    inference(superposition,[],[f57,f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f83,f60])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f33,f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f36,f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f80,f29])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))) )),
% 0.20/0.58    inference(superposition,[],[f78,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f32,f35,f51])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f77,f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) )),
% 0.20/0.58    inference(superposition,[],[f38,f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.58    inference(forward_demodulation,[],[f58,f31])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 0.20/0.58    inference(definition_unfolding,[],[f27,f56,f51,f56,f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f30,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f34,f54])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f50,f51,f49,f56])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.58    inference(superposition,[],[f60,f84])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f93,f31])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))),
% 0.20/0.58    inference(forward_demodulation,[],[f90,f88])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 0.20/0.58    inference(superposition,[],[f59,f84])).
% 0.20/0.58  fof(f620,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.58    inference(superposition,[],[f57,f568])).
% 0.20/0.58  fof(f568,plain,(
% 0.20/0.58    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(backward_demodulation,[],[f380,f567])).
% 0.20/0.58  fof(f567,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.58    inference(forward_demodulation,[],[f565,f479])).
% 0.20/0.58  fof(f479,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f464,f29])).
% 0.20/0.58  fof(f464,plain,(
% 0.20/0.58    k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(superposition,[],[f341,f331])).
% 0.20/0.58  fof(f331,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f330,f329])).
% 0.20/0.58  fof(f329,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 0.20/0.58    inference(forward_demodulation,[],[f323,f31])).
% 0.20/0.58  fof(f323,plain,(
% 0.20/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 0.20/0.58    inference(superposition,[],[f60,f95])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f91,f38])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) )),
% 0.20/0.58    inference(superposition,[],[f38,f84])).
% 0.20/0.58  fof(f330,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))))),
% 0.20/0.58    inference(forward_demodulation,[],[f324,f31])).
% 0.20/0.58  fof(f324,plain,(
% 0.20/0.58    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))),
% 0.20/0.58    inference(superposition,[],[f59,f95])).
% 0.20/0.58  fof(f341,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 0.20/0.58    inference(superposition,[],[f38,f331])).
% 0.20/0.58  fof(f565,plain,(
% 0.20/0.58    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(superposition,[],[f110,f398])).
% 0.20/0.58  fof(f398,plain,(
% 0.20/0.58    k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.58    inference(forward_demodulation,[],[f390,f29])).
% 0.20/0.58  fof(f390,plain,(
% 0.20/0.58    k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 0.20/0.58    inference(superposition,[],[f282,f103])).
% 0.20/0.58  fof(f282,plain,(
% 0.20/0.58    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),X0)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f237,f269])).
% 0.20/0.58  fof(f269,plain,(
% 0.20/0.58    ( ! [X1] : (k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1) = k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,X1)) )),
% 0.20/0.58    inference(backward_demodulation,[],[f220,f268])).
% 0.20/0.58  fof(f268,plain,(
% 0.20/0.58    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,X1)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f266,f57])).
% 0.20/0.59  fof(f266,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1))))) )),
% 0.20/0.59    inference(superposition,[],[f57,f223])).
% 0.20/0.59  fof(f223,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f176,f221])).
% 0.20/0.59  fof(f221,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f174,f220])).
% 0.20/0.59  fof(f174,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f172,f57])).
% 0.20/0.59  fof(f172,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1))))) )),
% 0.20/0.59    inference(superposition,[],[f57,f142])).
% 0.20/0.59  fof(f142,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f111,f141])).
% 0.20/0.59  fof(f141,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,X1)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f139,f57])).
% 0.20/0.59  fof(f139,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1))))) )),
% 0.20/0.59    inference(superposition,[],[f57,f111])).
% 0.20/0.59  fof(f111,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1)),
% 0.20/0.59    inference(superposition,[],[f104,f29])).
% 0.20/0.59  fof(f104,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k1_xboole_0)),
% 0.20/0.59    inference(forward_demodulation,[],[f98,f103])).
% 0.20/0.59  fof(f98,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.59    inference(superposition,[],[f57,f92])).
% 0.20/0.59  fof(f176,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f142,f175])).
% 0.20/0.59  fof(f175,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,X1) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,X1)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f141,f174])).
% 0.20/0.59  fof(f220,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,X1)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f218,f57])).
% 0.20/0.59  fof(f218,plain,(
% 0.20/0.59    ( ! [X1] : (k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,X1) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1))))) )),
% 0.20/0.59    inference(superposition,[],[f57,f176])).
% 0.20/0.59  fof(f237,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),X0)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f213,f221])).
% 0.20/0.59  fof(f213,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f212,f38])).
% 0.20/0.59  fof(f212,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) )),
% 0.20/0.59    inference(superposition,[],[f38,f180])).
% 0.20/0.59  fof(f180,plain,(
% 0.20/0.59    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f146,f175])).
% 0.20/0.59  fof(f146,plain,(
% 0.20/0.59    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f119,f141])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1)),
% 0.20/0.59    inference(backward_demodulation,[],[f88,f111])).
% 0.20/0.59  fof(f110,plain,(
% 0.20/0.59    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(superposition,[],[f38,f103])).
% 0.20/0.59  fof(f380,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.59    inference(superposition,[],[f60,f274])).
% 0.20/0.59  fof(f274,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK0,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f225,f269])).
% 0.20/0.59  fof(f225,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK0,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f178,f221])).
% 0.20/0.59  fof(f178,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f144,f175])).
% 0.20/0.59  fof(f144,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f117,f141])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f96,f111])).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 0.20/0.59    inference(equality_resolution,[],[f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 0.20/0.59    inference(equality_resolution,[],[f65])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.20/0.59    inference(definition_unfolding,[],[f43,f54])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (25026)------------------------------
% 0.20/0.59  % (25026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (25026)Termination reason: Refutation
% 1.78/0.59  
% 1.78/0.59  % (25026)Memory used [KB]: 11385
% 1.78/0.59  % (25026)Time elapsed: 0.165 s
% 1.78/0.59  % (25026)------------------------------
% 1.78/0.59  % (25026)------------------------------
% 1.78/0.59  % (25027)Refutation not found, incomplete strategy% (25027)------------------------------
% 1.78/0.59  % (25027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (25027)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.59  
% 1.78/0.59  % (25027)Memory used [KB]: 10618
% 1.78/0.59  % (25027)Time elapsed: 0.158 s
% 1.78/0.59  % (25027)------------------------------
% 1.78/0.59  % (25027)------------------------------
% 1.78/0.59  % (25017)Success in time 0.235 s
%------------------------------------------------------------------------------
