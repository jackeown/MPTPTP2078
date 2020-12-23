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
% DateTime   : Thu Dec  3 12:38:46 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 500 expanded)
%              Number of leaves         :   21 ( 163 expanded)
%              Depth                    :   22
%              Number of atoms          :  218 ( 681 expanded)
%              Number of equality atoms :   68 ( 451 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f627,plain,(
    $false ),
    inference(subsumption_resolution,[],[f626,f39])).

fof(f39,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f626,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f623,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f623,plain,(
    ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f622,f216])).

fof(f216,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(backward_demodulation,[],[f166,f208])).

fof(f208,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f192,f139])).

fof(f139,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f129,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f129,plain,(
    ! [X7] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X7)) = X7 ),
    inference(superposition,[],[f76,f74])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f71,f71])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f192,plain,(
    ! [X8] : k5_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = X8 ),
    inference(forward_demodulation,[],[f187,f129])).

fof(f187,plain,(
    ! [X8] : k5_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X8)) ),
    inference(superposition,[],[f79,f129])).

fof(f79,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f50,f71,f71,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f166,plain,(
    ! [X8] : k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X8 ),
    inference(forward_demodulation,[],[f151,f139])).

fof(f151,plain,(
    ! [X8] : k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8))) = X8 ),
    inference(superposition,[],[f78,f74])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f71,f48])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f622,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(forward_demodulation,[],[f620,f534])).

fof(f534,plain,(
    ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6) ),
    inference(resolution,[],[f529,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f142,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f142,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f75,f129])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f529,plain,(
    ! [X6,X7] : r1_tarski(k5_xboole_0(X6,X6),X7) ),
    inference(resolution,[],[f524,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,sK3(k5_xboole_0(X1,X0),X2),X1)
      | r1_tarski(k5_xboole_0(X1,X0),X2) ) ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f524,plain,(
    ! [X2,X3] : ~ sP0(X3,X2,X3) ),
    inference(subsumption_resolution,[],[f517,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f517,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | ~ sP0(X3,X2,X3) ) ),
    inference(resolution,[],[f511,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f511,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k5_xboole_0(X3,X3))
      | r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k5_xboole_0(X3,X3)) ) ),
    inference(resolution,[],[f401,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f401,plain,(
    ! [X8,X7] :
      ( ~ sP0(k5_xboole_0(X7,X7),X8,X7)
      | r2_hidden(X8,X7) ) ),
    inference(superposition,[],[f64,f389])).

fof(f389,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f388,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f388,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ) ),
    inference(condensation,[],[f376])).

fof(f376,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f147,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f103,f78])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f77,f51])).

fof(f620,plain,
    ( sK2 != k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[],[f596,f51])).

fof(f596,plain,(
    sK2 != k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(superposition,[],[f73,f148])).

fof(f148,plain,(
    ! [X2,X3] : k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(superposition,[],[f78,f76])).

fof(f73,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f40,f71,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f70])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4827)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (4819)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (4835)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (4836)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4817)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4818)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (4823)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4812)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4834)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4816)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4834)Refutation not found, incomplete strategy% (4834)------------------------------
% 0.21/0.54  % (4834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4834)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4834)Memory used [KB]: 10746
% 0.21/0.54  % (4834)Time elapsed: 0.131 s
% 0.21/0.54  % (4834)------------------------------
% 0.21/0.54  % (4834)------------------------------
% 0.21/0.54  % (4831)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (4814)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (4825)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (4815)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4822)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (4822)Refutation not found, incomplete strategy% (4822)------------------------------
% 0.21/0.55  % (4822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4822)Memory used [KB]: 10618
% 0.21/0.55  % (4822)Time elapsed: 0.132 s
% 0.21/0.55  % (4822)------------------------------
% 0.21/0.55  % (4822)------------------------------
% 0.21/0.55  % (4828)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (4838)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (4840)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (4826)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (4839)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (4841)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (4820)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.55  % (4830)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.56  % (4832)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (4824)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (4813)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.48/0.56  % (4837)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (4833)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.57  % (4839)Refutation found. Thanks to Tanya!
% 1.48/0.57  % SZS status Theorem for theBenchmark
% 1.48/0.57  % SZS output start Proof for theBenchmark
% 1.48/0.57  fof(f627,plain,(
% 1.48/0.57    $false),
% 1.48/0.57    inference(subsumption_resolution,[],[f626,f39])).
% 1.48/0.57  fof(f39,plain,(
% 1.48/0.57    r2_hidden(sK1,sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f27])).
% 1.48/0.57  fof(f27,plain,(
% 1.48/0.57    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 1.48/0.57  fof(f26,plain,(
% 1.48/0.57    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f20,plain,(
% 1.48/0.57    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f19])).
% 1.48/0.57  fof(f19,negated_conjecture,(
% 1.48/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.48/0.57    inference(negated_conjecture,[],[f18])).
% 1.48/0.57  fof(f18,conjecture,(
% 1.48/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.48/0.57  fof(f626,plain,(
% 1.48/0.57    ~r2_hidden(sK1,sK2)),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f624])).
% 1.48/0.57  fof(f624,plain,(
% 1.48/0.57    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.48/0.57    inference(resolution,[],[f623,f80])).
% 1.48/0.57  fof(f80,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f67,f70])).
% 1.48/0.57  fof(f70,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f47,f69])).
% 1.48/0.57  fof(f69,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f58,f68])).
% 1.48/0.57  fof(f68,plain,(
% 1.48/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f15])).
% 1.48/0.57  fof(f15,axiom,(
% 1.48/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.48/0.57  fof(f58,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f14])).
% 1.48/0.57  fof(f14,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.57  fof(f47,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f13])).
% 1.48/0.57  fof(f13,axiom,(
% 1.48/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.57  fof(f67,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f38])).
% 1.48/0.57  fof(f38,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.57    inference(flattening,[],[f37])).
% 1.48/0.57  fof(f37,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.48/0.57    inference(nnf_transformation,[],[f17])).
% 1.48/0.57  fof(f17,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.48/0.57  fof(f623,plain,(
% 1.48/0.57    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.48/0.57    inference(subsumption_resolution,[],[f622,f216])).
% 1.48/0.57  fof(f216,plain,(
% 1.48/0.57    ( ! [X8] : (k5_xboole_0(X8,k1_xboole_0) = X8) )),
% 1.48/0.57    inference(backward_demodulation,[],[f166,f208])).
% 1.48/0.57  fof(f208,plain,(
% 1.48/0.57    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.48/0.57    inference(superposition,[],[f192,f139])).
% 1.48/0.57  fof(f139,plain,(
% 1.48/0.57    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 1.48/0.57    inference(superposition,[],[f129,f77])).
% 1.48/0.57  fof(f77,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.48/0.57    inference(definition_unfolding,[],[f45,f71])).
% 1.48/0.57  fof(f71,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f46,f70])).
% 1.48/0.57  fof(f46,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f16])).
% 1.48/0.57  fof(f16,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.48/0.57  fof(f45,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f7])).
% 1.48/0.57  fof(f7,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.48/0.57  fof(f129,plain,(
% 1.48/0.57    ( ! [X7] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X7)) = X7) )),
% 1.48/0.57    inference(superposition,[],[f76,f74])).
% 1.48/0.57  fof(f74,plain,(
% 1.48/0.57    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.48/0.57    inference(definition_unfolding,[],[f41,f71])).
% 1.48/0.57  fof(f41,plain,(
% 1.48/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.57    inference(cnf_transformation,[],[f6])).
% 1.48/0.57  fof(f6,axiom,(
% 1.48/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.48/0.57  fof(f76,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f44,f71,f71])).
% 1.48/0.57  fof(f44,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f1])).
% 1.48/0.57  fof(f1,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.48/0.57  fof(f192,plain,(
% 1.48/0.57    ( ! [X8] : (k5_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = X8) )),
% 1.48/0.57    inference(forward_demodulation,[],[f187,f129])).
% 1.48/0.57  fof(f187,plain,(
% 1.48/0.57    ( ! [X8] : (k5_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X8))) )),
% 1.48/0.57    inference(superposition,[],[f79,f129])).
% 1.48/0.57  fof(f79,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f50,f71,f71,f48])).
% 1.48/0.57  fof(f48,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f5])).
% 1.48/0.57  fof(f5,axiom,(
% 1.48/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.57  fof(f50,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f9])).
% 1.48/0.57  fof(f9,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.48/0.57  fof(f166,plain,(
% 1.48/0.57    ( ! [X8] : (k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X8) )),
% 1.48/0.57    inference(forward_demodulation,[],[f151,f139])).
% 1.48/0.57  fof(f151,plain,(
% 1.48/0.57    ( ! [X8] : (k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8))) = X8) )),
% 1.48/0.57    inference(superposition,[],[f78,f74])).
% 1.48/0.57  fof(f78,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f49,f71,f48])).
% 1.48/0.57  fof(f49,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f11])).
% 1.48/0.57  fof(f11,axiom,(
% 1.48/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.48/0.57  fof(f622,plain,(
% 1.48/0.57    sK2 != k5_xboole_0(sK2,k1_xboole_0) | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.48/0.57    inference(forward_demodulation,[],[f620,f534])).
% 1.48/0.57  fof(f534,plain,(
% 1.48/0.57    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) )),
% 1.48/0.57    inference(resolution,[],[f529,f144])).
% 1.48/0.57  fof(f144,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.48/0.57    inference(resolution,[],[f142,f54])).
% 1.48/0.57  fof(f54,plain,(
% 1.48/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f29])).
% 1.48/0.57  fof(f29,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(flattening,[],[f28])).
% 1.48/0.57  fof(f28,plain,(
% 1.48/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.57    inference(nnf_transformation,[],[f4])).
% 1.48/0.57  fof(f4,axiom,(
% 1.48/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.57  fof(f142,plain,(
% 1.48/0.57    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.48/0.57    inference(superposition,[],[f75,f129])).
% 1.48/0.57  fof(f75,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.48/0.57    inference(definition_unfolding,[],[f43,f71])).
% 1.48/0.57  fof(f43,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.48/0.57    inference(cnf_transformation,[],[f10])).
% 1.48/0.57  fof(f10,axiom,(
% 1.48/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.48/0.57  fof(f529,plain,(
% 1.48/0.57    ( ! [X6,X7] : (r1_tarski(k5_xboole_0(X6,X6),X7)) )),
% 1.48/0.57    inference(resolution,[],[f524,f89])).
% 1.48/0.57  fof(f89,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (sP0(X0,sK3(k5_xboole_0(X1,X0),X2),X1) | r1_tarski(k5_xboole_0(X1,X0),X2)) )),
% 1.48/0.57    inference(resolution,[],[f63,f56])).
% 1.48/0.57  fof(f56,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f33])).
% 1.48/0.57  fof(f33,plain,(
% 1.48/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.48/0.57  fof(f32,plain,(
% 1.48/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.48/0.57    introduced(choice_axiom,[])).
% 1.48/0.57  fof(f31,plain,(
% 1.48/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.57    inference(rectify,[],[f30])).
% 1.48/0.57  fof(f30,plain,(
% 1.48/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/0.57    inference(nnf_transformation,[],[f22])).
% 1.48/0.57  fof(f22,plain,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.57    inference(ennf_transformation,[],[f2])).
% 1.48/0.57  fof(f2,axiom,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.57  fof(f63,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f36])).
% 1.48/0.57  fof(f36,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.48/0.57    inference(nnf_transformation,[],[f25])).
% 1.48/0.57  fof(f25,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.48/0.57    inference(definition_folding,[],[f23,f24])).
% 1.48/0.57  fof(f24,plain,(
% 1.48/0.57    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.48/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.57  fof(f23,plain,(
% 1.48/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.48/0.57    inference(ennf_transformation,[],[f3])).
% 1.48/0.57  fof(f3,axiom,(
% 1.48/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.48/0.57  fof(f524,plain,(
% 1.48/0.57    ( ! [X2,X3] : (~sP0(X3,X2,X3)) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f517,f60])).
% 1.48/0.57  fof(f60,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f35])).
% 1.48/0.57  fof(f35,plain,(
% 1.48/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 1.48/0.57    inference(rectify,[],[f34])).
% 1.48/0.57  fof(f34,plain,(
% 1.48/0.57    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.48/0.57    inference(nnf_transformation,[],[f24])).
% 1.48/0.57  fof(f517,plain,(
% 1.48/0.57    ( ! [X2,X3] : (r2_hidden(X2,X3) | ~sP0(X3,X2,X3)) )),
% 1.48/0.57    inference(resolution,[],[f511,f64])).
% 1.48/0.57  fof(f64,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f36])).
% 1.48/0.57  fof(f511,plain,(
% 1.48/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,X3)) | r2_hidden(X2,X3)) )),
% 1.48/0.57    inference(duplicate_literal_removal,[],[f502])).
% 1.48/0.57  fof(f502,plain,(
% 1.48/0.57    ( ! [X2,X3] : (r2_hidden(X2,X3) | r2_hidden(X2,X3) | ~r2_hidden(X2,k5_xboole_0(X3,X3))) )),
% 1.48/0.57    inference(resolution,[],[f401,f62])).
% 1.48/0.57  fof(f62,plain,(
% 1.48/0.57    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f35])).
% 1.48/0.57  fof(f401,plain,(
% 1.48/0.57    ( ! [X8,X7] : (~sP0(k5_xboole_0(X7,X7),X8,X7) | r2_hidden(X8,X7)) )),
% 1.48/0.57    inference(superposition,[],[f64,f389])).
% 1.48/0.57  fof(f389,plain,(
% 1.48/0.57    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.48/0.57    inference(subsumption_resolution,[],[f388,f83])).
% 1.48/0.57  fof(f83,plain,(
% 1.48/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.57    inference(equality_resolution,[],[f53])).
% 1.48/0.57  fof(f53,plain,(
% 1.48/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.57    inference(cnf_transformation,[],[f29])).
% 1.48/0.57  fof(f388,plain,(
% 1.48/0.57    ( ! [X0] : (~r1_tarski(X0,X0) | k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.48/0.57    inference(condensation,[],[f376])).
% 1.48/0.57  fof(f376,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 1.48/0.57    inference(superposition,[],[f147,f51])).
% 1.48/0.57  fof(f51,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f21])).
% 1.48/0.57  fof(f21,plain,(
% 1.48/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.57    inference(ennf_transformation,[],[f8])).
% 1.48/0.57  fof(f8,axiom,(
% 1.48/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.57  fof(f147,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(backward_demodulation,[],[f103,f78])).
% 1.48/0.57  fof(f103,plain,(
% 1.48/0.57    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.48/0.57    inference(superposition,[],[f77,f51])).
% 1.48/0.57  fof(f620,plain,(
% 1.48/0.57    sK2 != k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.48/0.57    inference(superposition,[],[f596,f51])).
% 1.48/0.57  fof(f596,plain,(
% 1.48/0.57    sK2 != k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)))),
% 1.48/0.57    inference(superposition,[],[f73,f148])).
% 1.48/0.57  fof(f148,plain,(
% 1.48/0.57    ( ! [X2,X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) )),
% 1.48/0.57    inference(superposition,[],[f78,f76])).
% 1.48/0.57  fof(f73,plain,(
% 1.48/0.57    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.48/0.57    inference(definition_unfolding,[],[f40,f71,f72])).
% 1.48/0.57  fof(f72,plain,(
% 1.48/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.48/0.57    inference(definition_unfolding,[],[f42,f70])).
% 1.48/0.57  fof(f42,plain,(
% 1.48/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.57    inference(cnf_transformation,[],[f12])).
% 1.48/0.57  fof(f12,axiom,(
% 1.48/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.57  fof(f40,plain,(
% 1.48/0.57    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.48/0.57    inference(cnf_transformation,[],[f27])).
% 1.48/0.57  % SZS output end Proof for theBenchmark
% 1.48/0.57  % (4839)------------------------------
% 1.48/0.57  % (4839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (4839)Termination reason: Refutation
% 1.48/0.57  
% 1.48/0.57  % (4839)Memory used [KB]: 6524
% 1.48/0.57  % (4839)Time elapsed: 0.148 s
% 1.48/0.57  % (4839)------------------------------
% 1.48/0.57  % (4839)------------------------------
% 1.48/0.57  % (4811)Success in time 0.204 s
%------------------------------------------------------------------------------
