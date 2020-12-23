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
% DateTime   : Thu Dec  3 12:38:45 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 846 expanded)
%              Number of leaves         :   19 ( 273 expanded)
%              Depth                    :   24
%              Number of atoms          :  245 (1647 expanded)
%              Number of equality atoms :   62 ( 744 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f570,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f560,f569])).

fof(f569,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f529,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f529,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl5_2 ),
    inference(backward_demodulation,[],[f127,f521])).

fof(f521,plain,(
    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(resolution,[],[f514,f39])).

fof(f39,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f514,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(X4,X4,X4,X4,sK1))) ) ),
    inference(resolution,[],[f501,f156])).

fof(f156,plain,(
    ! [X0] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,sK1),sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f79,f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f501,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f482,f74])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f482,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f278,f472])).

fof(f472,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f461,f82])).

fof(f461,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f453,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f453,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(resolution,[],[f451,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f451,plain,(
    ! [X0] : sP0(X0,X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X0] :
      ( sP0(X0,X0,k1_xboole_0)
      | sP0(X0,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f299,f298])).

fof(f298,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4(X6,X7,k1_xboole_0),X6)
      | sP0(X6,X7,k1_xboole_0) ) ),
    inference(resolution,[],[f294,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f294,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f284])).

fof(f284,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f95,f281])).

fof(f281,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6 ),
    inference(forward_demodulation,[],[f279,f187])).

fof(f187,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f75,f74])).

fof(f75,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f71,f71])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f279,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X6)) ),
    inference(superposition,[],[f76,f187])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f48,f71,f71,f47])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f58,f84])).

fof(f84,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f47])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f299,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(X8,X9,k1_xboole_0),X9)
      | sP0(X8,X9,k1_xboole_0) ) ),
    inference(resolution,[],[f294,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f278,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f76,f49])).

fof(f127,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_2
  <=> r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f560,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f528,f82])).

fof(f528,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl5_1 ),
    inference(backward_demodulation,[],[f123,f521])).

fof(f123,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_1
  <=> r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f131,plain,
    ( ~ spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f130,f121,f125])).

fof(f130,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f129,f75])).

fof(f129,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | ~ r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f117,f75])).

fof(f117,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)))
    | ~ r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),sK2) ),
    inference(extensionality_resolution,[],[f52,f73])).

fof(f73,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f40,f71,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (24985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (24977)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (24985)Refutation not found, incomplete strategy% (24985)------------------------------
% 0.21/0.51  % (24985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24985)Memory used [KB]: 1663
% 0.21/0.51  % (24985)Time elapsed: 0.089 s
% 0.21/0.51  % (24985)------------------------------
% 0.21/0.51  % (24985)------------------------------
% 0.21/0.54  % (24986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (24966)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (24986)Refutation not found, incomplete strategy% (24986)------------------------------
% 0.21/0.55  % (24986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24986)Memory used [KB]: 10746
% 0.21/0.55  % (24986)Time elapsed: 0.074 s
% 0.21/0.55  % (24986)------------------------------
% 0.21/0.55  % (24986)------------------------------
% 0.21/0.55  % (24969)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (24968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (24973)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (24984)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (24970)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (24981)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (24974)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (24978)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (24993)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (24974)Refutation not found, incomplete strategy% (24974)------------------------------
% 0.21/0.56  % (24974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24974)Memory used [KB]: 10618
% 0.21/0.56  % (24974)Time elapsed: 0.135 s
% 0.21/0.56  % (24974)------------------------------
% 0.21/0.56  % (24974)------------------------------
% 0.21/0.56  % (24965)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (24967)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (24982)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (24989)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (24976)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (24992)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (24991)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (24984)Refutation not found, incomplete strategy% (24984)------------------------------
% 0.21/0.58  % (24984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (24984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (24984)Memory used [KB]: 10746
% 0.21/0.58  % (24984)Time elapsed: 0.169 s
% 0.21/0.58  % (24984)------------------------------
% 0.21/0.58  % (24984)------------------------------
% 0.21/0.58  % (24990)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (24975)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (24983)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % (24980)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.59  % (24972)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (24988)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.59  % (24964)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.84/0.61  % (24987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.84/0.61  % (24979)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.84/0.61  % (24971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.84/0.62  % (24976)Refutation found. Thanks to Tanya!
% 1.84/0.62  % SZS status Theorem for theBenchmark
% 1.84/0.62  % SZS output start Proof for theBenchmark
% 1.84/0.62  fof(f570,plain,(
% 1.84/0.62    $false),
% 1.84/0.62    inference(avatar_sat_refutation,[],[f131,f560,f569])).
% 1.84/0.62  fof(f569,plain,(
% 1.84/0.62    spl5_2),
% 1.84/0.62    inference(avatar_contradiction_clause,[],[f567])).
% 1.84/0.62  fof(f567,plain,(
% 1.84/0.62    $false | spl5_2),
% 1.84/0.62    inference(resolution,[],[f529,f82])).
% 1.84/0.62  fof(f82,plain,(
% 1.84/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.62    inference(equality_resolution,[],[f51])).
% 1.84/0.62  fof(f51,plain,(
% 1.84/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.62    inference(cnf_transformation,[],[f26])).
% 1.84/0.62  fof(f26,plain,(
% 1.84/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.62    inference(flattening,[],[f25])).
% 1.84/0.62  fof(f25,plain,(
% 1.84/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.62    inference(nnf_transformation,[],[f4])).
% 1.84/0.62  fof(f4,axiom,(
% 1.84/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.62  fof(f529,plain,(
% 1.84/0.62    ~r1_tarski(sK2,sK2) | spl5_2),
% 1.84/0.62    inference(backward_demodulation,[],[f127,f521])).
% 1.84/0.62  fof(f521,plain,(
% 1.84/0.62    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.84/0.62    inference(resolution,[],[f514,f39])).
% 1.84/0.62  fof(f39,plain,(
% 1.84/0.62    r2_hidden(sK1,sK2)),
% 1.84/0.62    inference(cnf_transformation,[],[f24])).
% 1.84/0.62  fof(f24,plain,(
% 1.84/0.62    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.84/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f23])).
% 1.84/0.62  fof(f23,plain,(
% 1.84/0.62    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f18,plain,(
% 1.84/0.62    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.84/0.62    inference(ennf_transformation,[],[f17])).
% 1.84/0.62  fof(f17,negated_conjecture,(
% 1.84/0.62    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.84/0.62    inference(negated_conjecture,[],[f16])).
% 1.84/0.62  fof(f16,conjecture,(
% 1.84/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.84/0.62  fof(f514,plain,(
% 1.84/0.62    ( ! [X4] : (~r2_hidden(X4,sK2) | sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(X4,X4,X4,X4,sK1)))) )),
% 1.84/0.62    inference(resolution,[],[f501,f156])).
% 1.84/0.62  fof(f156,plain,(
% 1.84/0.62    ( ! [X0] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,sK1),sK2) | ~r2_hidden(X0,sK2)) )),
% 1.84/0.62    inference(resolution,[],[f79,f39])).
% 1.84/0.62  fof(f79,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f67,f70])).
% 1.84/0.62  fof(f70,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f46,f69])).
% 1.84/0.62  fof(f69,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f56,f68])).
% 1.84/0.62  fof(f68,plain,(
% 1.84/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f13])).
% 1.84/0.62  fof(f13,axiom,(
% 1.84/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.84/0.62  fof(f56,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f12])).
% 1.84/0.62  fof(f12,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.84/0.62  fof(f46,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f11])).
% 1.84/0.62  fof(f11,axiom,(
% 1.84/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.84/0.62  fof(f67,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f38])).
% 1.84/0.62  fof(f38,plain,(
% 1.84/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.84/0.62    inference(flattening,[],[f37])).
% 1.84/0.62  fof(f37,plain,(
% 1.84/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.84/0.62    inference(nnf_transformation,[],[f15])).
% 1.84/0.62  fof(f15,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.84/0.62  fof(f501,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1) )),
% 1.84/0.62    inference(forward_demodulation,[],[f482,f74])).
% 1.84/0.62  fof(f74,plain,(
% 1.84/0.62    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.84/0.62    inference(definition_unfolding,[],[f42,f71])).
% 1.84/0.62  fof(f71,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f45,f70])).
% 1.84/0.62  fof(f45,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f14])).
% 1.84/0.62  fof(f14,axiom,(
% 1.84/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.84/0.62  fof(f42,plain,(
% 1.84/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.62    inference(cnf_transformation,[],[f6])).
% 1.84/0.62  fof(f6,axiom,(
% 1.84/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.84/0.62  fof(f482,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(backward_demodulation,[],[f278,f472])).
% 1.84/0.62  fof(f472,plain,(
% 1.84/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.84/0.62    inference(resolution,[],[f461,f82])).
% 1.84/0.62  fof(f461,plain,(
% 1.84/0.62    ( ! [X0] : (~r1_tarski(X0,X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.84/0.62    inference(superposition,[],[f453,f49])).
% 1.84/0.62  fof(f49,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f19])).
% 1.84/0.62  fof(f19,plain,(
% 1.84/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.84/0.62    inference(ennf_transformation,[],[f7])).
% 1.84/0.62  fof(f7,axiom,(
% 1.84/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.84/0.62  fof(f453,plain,(
% 1.84/0.62    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.84/0.62    inference(resolution,[],[f451,f77])).
% 1.84/0.62  fof(f77,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.84/0.62    inference(definition_unfolding,[],[f64,f47])).
% 1.84/0.62  fof(f47,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f5])).
% 1.84/0.62  fof(f5,axiom,(
% 1.84/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.84/0.62  fof(f64,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f36])).
% 1.84/0.62  fof(f36,plain,(
% 1.84/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.84/0.62    inference(nnf_transformation,[],[f22])).
% 1.84/0.62  fof(f22,plain,(
% 1.84/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.84/0.62    inference(definition_folding,[],[f3,f21])).
% 1.84/0.62  fof(f21,plain,(
% 1.84/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.84/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.84/0.62  fof(f3,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.84/0.62  fof(f451,plain,(
% 1.84/0.62    ( ! [X0] : (sP0(X0,X0,k1_xboole_0)) )),
% 1.84/0.62    inference(duplicate_literal_removal,[],[f446])).
% 1.84/0.62  fof(f446,plain,(
% 1.84/0.62    ( ! [X0] : (sP0(X0,X0,k1_xboole_0) | sP0(X0,X0,k1_xboole_0)) )),
% 1.84/0.62    inference(resolution,[],[f299,f298])).
% 1.84/0.62  fof(f298,plain,(
% 1.84/0.62    ( ! [X6,X7] : (~r2_hidden(sK4(X6,X7,k1_xboole_0),X6) | sP0(X6,X7,k1_xboole_0)) )),
% 1.84/0.62    inference(resolution,[],[f294,f61])).
% 1.84/0.62  fof(f61,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f35])).
% 1.84/0.62  fof(f35,plain,(
% 1.84/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.84/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.84/0.62  fof(f34,plain,(
% 1.84/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f33,plain,(
% 1.84/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.84/0.62    inference(rectify,[],[f32])).
% 1.84/0.62  fof(f32,plain,(
% 1.84/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.84/0.62    inference(flattening,[],[f31])).
% 1.84/0.62  fof(f31,plain,(
% 1.84/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.84/0.62    inference(nnf_transformation,[],[f21])).
% 1.84/0.62  fof(f294,plain,(
% 1.84/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.84/0.62    inference(condensation,[],[f284])).
% 1.84/0.62  fof(f284,plain,(
% 1.84/0.62    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.84/0.62    inference(superposition,[],[f95,f281])).
% 1.84/0.62  fof(f281,plain,(
% 1.84/0.62    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6) )),
% 1.84/0.62    inference(forward_demodulation,[],[f279,f187])).
% 1.84/0.62  fof(f187,plain,(
% 1.84/0.62    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.84/0.62    inference(superposition,[],[f75,f74])).
% 1.84/0.62  fof(f75,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f44,f71,f71])).
% 1.84/0.62  fof(f44,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f1])).
% 1.84/0.62  fof(f1,axiom,(
% 1.84/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.84/0.62  fof(f279,plain,(
% 1.84/0.62    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X6))) )),
% 1.84/0.62    inference(superposition,[],[f76,f187])).
% 1.84/0.62  fof(f76,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f48,f71,f71,f47])).
% 1.84/0.62  fof(f48,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f9])).
% 1.84/0.62  fof(f9,axiom,(
% 1.84/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.84/0.62  fof(f95,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r2_hidden(X0,X2)) )),
% 1.84/0.62    inference(resolution,[],[f58,f84])).
% 1.84/0.62  fof(f84,plain,(
% 1.84/0.62    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.84/0.62    inference(equality_resolution,[],[f78])).
% 1.84/0.62  fof(f78,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.84/0.62    inference(definition_unfolding,[],[f63,f47])).
% 1.84/0.62  fof(f63,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.84/0.62    inference(cnf_transformation,[],[f36])).
% 1.84/0.62  fof(f58,plain,(
% 1.84/0.62    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f35])).
% 1.84/0.62  fof(f299,plain,(
% 1.84/0.62    ( ! [X8,X9] : (r2_hidden(sK4(X8,X9,k1_xboole_0),X9) | sP0(X8,X9,k1_xboole_0)) )),
% 1.84/0.62    inference(resolution,[],[f294,f60])).
% 1.84/0.62  fof(f60,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f35])).
% 1.84/0.62  fof(f278,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(superposition,[],[f76,f49])).
% 1.84/0.62  fof(f127,plain,(
% 1.84/0.62    ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | spl5_2),
% 1.84/0.62    inference(avatar_component_clause,[],[f125])).
% 1.84/0.62  fof(f125,plain,(
% 1.84/0.62    spl5_2 <=> r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.84/0.62  fof(f560,plain,(
% 1.84/0.62    spl5_1),
% 1.84/0.62    inference(avatar_contradiction_clause,[],[f558])).
% 1.84/0.62  fof(f558,plain,(
% 1.84/0.62    $false | spl5_1),
% 1.84/0.62    inference(resolution,[],[f528,f82])).
% 1.84/0.62  fof(f528,plain,(
% 1.84/0.62    ~r1_tarski(sK2,sK2) | spl5_1),
% 1.84/0.62    inference(backward_demodulation,[],[f123,f521])).
% 1.84/0.62  fof(f123,plain,(
% 1.84/0.62    ~r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2) | spl5_1),
% 1.84/0.62    inference(avatar_component_clause,[],[f121])).
% 1.84/0.62  fof(f121,plain,(
% 1.84/0.62    spl5_1 <=> r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2)),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.84/0.62  fof(f131,plain,(
% 1.84/0.62    ~spl5_2 | ~spl5_1),
% 1.84/0.62    inference(avatar_split_clause,[],[f130,f121,f125])).
% 1.84/0.62  fof(f130,plain,(
% 1.84/0.62    ~r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),sK2) | ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.84/0.62    inference(forward_demodulation,[],[f129,f75])).
% 1.84/0.62  fof(f129,plain,(
% 1.84/0.62    ~r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | ~r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),sK2)),
% 1.84/0.62    inference(forward_demodulation,[],[f117,f75])).
% 1.84/0.62  fof(f117,plain,(
% 1.84/0.62    ~r1_tarski(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))) | ~r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),sK2)),
% 1.84/0.62    inference(extensionality_resolution,[],[f52,f73])).
% 1.84/0.62  fof(f73,plain,(
% 1.84/0.62    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.84/0.62    inference(definition_unfolding,[],[f40,f71,f72])).
% 1.84/0.62  fof(f72,plain,(
% 1.84/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f43,f70])).
% 1.84/0.62  fof(f43,plain,(
% 1.84/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f10])).
% 1.84/0.62  fof(f10,axiom,(
% 1.84/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.84/0.62  fof(f40,plain,(
% 1.84/0.62    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.84/0.62    inference(cnf_transformation,[],[f24])).
% 1.84/0.62  fof(f52,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f26])).
% 1.84/0.62  % SZS output end Proof for theBenchmark
% 1.84/0.62  % (24976)------------------------------
% 1.84/0.62  % (24976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (24976)Termination reason: Refutation
% 1.84/0.62  
% 1.84/0.62  % (24976)Memory used [KB]: 6524
% 1.84/0.62  % (24976)Time elapsed: 0.195 s
% 1.84/0.62  % (24976)------------------------------
% 1.84/0.62  % (24976)------------------------------
% 2.00/0.62  % (24963)Success in time 0.258 s
%------------------------------------------------------------------------------
