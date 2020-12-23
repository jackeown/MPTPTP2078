%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:41 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   86 (7048 expanded)
%              Number of leaves         :   12 (2321 expanded)
%              Depth                    :   26
%              Number of atoms          :  199 (16158 expanded)
%              Number of equality atoms :  147 (12351 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f250,f208])).

fof(f208,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f63,f191])).

fof(f191,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f186,f185])).

fof(f185,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f184,f135])).

fof(f135,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f63,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( sK0 != sK0
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f121,f69])).

fof(f69,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f29,f67])).

fof(f67,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f65,f66])).

fof(f66,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f65,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f30,f64])).

fof(f64,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f29,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f121,plain,(
    ! [X4,X3] :
      ( k4_tarski(X4,X3) != X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X4,X3] :
      ( k4_tarski(X4,X3) != X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(superposition,[],[f75,f103])).

fof(f103,plain,(
    ! [X0] :
      ( sK3(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(resolution,[],[f102,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f102,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k2_enumset1(X5,X5,X5,X5))
      | X5 = X6 ) ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,(
    ! [X6,X5] :
      ( k2_enumset1(X5,X5,X5,X5) != k2_enumset1(X5,X5,X5,X5)
      | ~ r2_hidden(X6,k2_enumset1(X5,X5,X5,X5))
      | X5 = X6 ) ),
    inference(superposition,[],[f57,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f43,f52,f52,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( sK3(X1) != k4_tarski(X0,sK3(X1))
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK3(X1) != k4_tarski(X0,sK3(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f35,f33])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f184,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f169,f134])).

fof(f134,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0))
      | sK0 = sK1 ) ),
    inference(superposition,[],[f62,f127])).

fof(f62,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f169,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f33,f167])).

fof(f167,plain,
    ( sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f165,f135])).

fof(f165,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK1
    | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK1
    | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK0 = sK1 ),
    inference(resolution,[],[f136,f138])).

fof(f138,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | sK0 = X8
      | sK0 = sK1 ) ),
    inference(superposition,[],[f102,f127])).

fof(f136,plain,(
    ! [X6] :
      ( r2_hidden(sK3(k4_xboole_0(X6,k1_xboole_0)),X6)
      | k1_xboole_0 = k4_xboole_0(X6,k1_xboole_0)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f76,f127])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))),X0)
      | k1_xboole_0 = k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f186,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f149,f185])).

fof(f149,plain,
    ( sK0 != sK1
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f122,f29])).

fof(f122,plain,(
    ! [X2,X1] :
      ( k4_tarski(X1,X2) != X1
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X1] :
      ( k4_tarski(X1,X2) != X1
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(superposition,[],[f73,f103])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f34,f33])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f42,f52,f52,f52])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f250,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f241,f207])).

fof(f207,plain,(
    ! [X5] : ~ r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f62,f191])).

fof(f241,plain,
    ( r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f33,f239])).

fof(f239,plain,(
    sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f234,f208])).

fof(f234,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f209,f211])).

fof(f211,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | sK0 = X8 ) ),
    inference(superposition,[],[f102,f191])).

fof(f209,plain,(
    ! [X6] :
      ( r2_hidden(sK3(k4_xboole_0(X6,k1_xboole_0)),X6)
      | k1_xboole_0 = k4_xboole_0(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f76,f191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:04:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (9853)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.51  % (9869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.17/0.52  % (9859)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.53  % (9861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.17/0.53  % (9862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (9852)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.53  % (9869)Refutation not found, incomplete strategy% (9869)------------------------------
% 1.17/0.53  % (9869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.53  % (9869)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.53  
% 1.17/0.53  % (9869)Memory used [KB]: 1791
% 1.17/0.53  % (9869)Time elapsed: 0.118 s
% 1.17/0.53  % (9869)------------------------------
% 1.17/0.53  % (9869)------------------------------
% 1.34/0.53  % (9871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (9867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (9850)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (9855)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.54  % (9851)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (9850)Refutation not found, incomplete strategy% (9850)------------------------------
% 1.34/0.54  % (9850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (9850)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (9850)Memory used [KB]: 10746
% 1.34/0.54  % (9850)Time elapsed: 0.124 s
% 1.34/0.54  % (9850)------------------------------
% 1.34/0.54  % (9850)------------------------------
% 1.34/0.54  % (9854)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.54  % (9863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (9860)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (9849)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (9866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (9875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (9853)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f251,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(subsumption_resolution,[],[f250,f208])).
% 1.34/0.54  fof(f208,plain,(
% 1.34/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.54    inference(superposition,[],[f63,f191])).
% 1.34/0.54  fof(f191,plain,(
% 1.34/0.54    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.34/0.54    inference(forward_demodulation,[],[f186,f185])).
% 1.34/0.54  fof(f185,plain,(
% 1.34/0.54    sK0 = sK1),
% 1.34/0.54    inference(subsumption_resolution,[],[f184,f135])).
% 1.34/0.54  fof(f135,plain,(
% 1.34/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK1),
% 1.34/0.54    inference(superposition,[],[f63,f127])).
% 1.34/0.54  fof(f127,plain,(
% 1.34/0.54    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f126])).
% 1.34/0.54  fof(f126,plain,(
% 1.34/0.54    sK0 != sK0 | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.34/0.54    inference(superposition,[],[f121,f69])).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 1.34/0.54    inference(superposition,[],[f29,f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    sK0 = sK2 | sK0 = sK1),
% 1.34/0.54    inference(superposition,[],[f65,f66])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    k2_mcart_1(sK0) = sK2),
% 1.34/0.54    inference(superposition,[],[f32,f29])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.34/0.54    inference(backward_demodulation,[],[f30,f64])).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    k1_mcart_1(sK0) = sK1),
% 1.34/0.54    inference(superposition,[],[f31,f29])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f13])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,negated_conjecture,(
% 1.34/0.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.34/0.54    inference(negated_conjecture,[],[f15])).
% 1.34/0.54  fof(f15,conjecture,(
% 1.34/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    sK0 = k4_tarski(sK1,sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f121,plain,(
% 1.34/0.54    ( ! [X4,X3] : (k4_tarski(X4,X3) != X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f108])).
% 1.34/0.54  fof(f108,plain,(
% 1.34/0.54    ( ! [X4,X3] : (k4_tarski(X4,X3) != X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 1.34/0.54    inference(superposition,[],[f75,f103])).
% 1.34/0.54  fof(f103,plain,(
% 1.34/0.54    ( ! [X0] : (sK3(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.54    inference(resolution,[],[f102,f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X6,X5] : (~r2_hidden(X6,k2_enumset1(X5,X5,X5,X5)) | X5 = X6) )),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f99])).
% 1.34/0.54  fof(f99,plain,(
% 1.34/0.54    ( ! [X6,X5] : (k2_enumset1(X5,X5,X5,X5) != k2_enumset1(X5,X5,X5,X5) | ~r2_hidden(X6,k2_enumset1(X5,X5,X5,X5)) | X5 = X6) )),
% 1.34/0.54    inference(superposition,[],[f57,f59])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 1.34/0.54    inference(definition_unfolding,[],[f43,f52,f52,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f44,f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f47,f49])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.34/0.54    inference(nnf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.34/0.54  fof(f57,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f39,f52])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.34/0.54    inference(nnf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.34/0.54  fof(f75,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK3(X1) != k4_tarski(X0,sK3(X1)) | k1_xboole_0 = X1) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f74])).
% 1.34/0.54  fof(f74,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK3(X1) != k4_tarski(X0,sK3(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 1.34/0.54    inference(resolution,[],[f35,f33])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f184,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK1),
% 1.34/0.54    inference(subsumption_resolution,[],[f169,f134])).
% 1.34/0.54  fof(f134,plain,(
% 1.34/0.54    ( ! [X5] : (~r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0)) | sK0 = sK1) )),
% 1.34/0.54    inference(superposition,[],[f62,f127])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.34/0.54    inference(equality_resolution,[],[f54])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f37,f52])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.34/0.54    inference(flattening,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.34/0.54    inference(nnf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.34/0.54  fof(f169,plain,(
% 1.34/0.54    r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK1),
% 1.34/0.54    inference(superposition,[],[f33,f167])).
% 1.34/0.54  fof(f167,plain,(
% 1.34/0.54    sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)) | sK0 = sK1),
% 1.34/0.54    inference(subsumption_resolution,[],[f165,f135])).
% 1.34/0.54  fof(f165,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK1 | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f163])).
% 1.34/0.54  fof(f163,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK1 | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0)) | sK0 = sK1),
% 1.34/0.54    inference(resolution,[],[f136,f138])).
% 1.34/0.54  fof(f138,plain,(
% 1.34/0.54    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0) | sK0 = X8 | sK0 = sK1) )),
% 1.34/0.54    inference(superposition,[],[f102,f127])).
% 1.34/0.54  fof(f136,plain,(
% 1.34/0.54    ( ! [X6] : (r2_hidden(sK3(k4_xboole_0(X6,k1_xboole_0)),X6) | k1_xboole_0 = k4_xboole_0(X6,k1_xboole_0) | sK0 = sK1) )),
% 1.34/0.54    inference(superposition,[],[f76,f127])).
% 1.34/0.54  fof(f76,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))),X0) | k1_xboole_0 = k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.34/0.54    inference(resolution,[],[f55,f33])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f36,f52])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f186,plain,(
% 1.34/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.34/0.54    inference(subsumption_resolution,[],[f149,f185])).
% 1.34/0.54  fof(f149,plain,(
% 1.34/0.54    sK0 != sK1 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.34/0.54    inference(superposition,[],[f122,f29])).
% 1.34/0.54  fof(f122,plain,(
% 1.34/0.54    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1 | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f107])).
% 1.34/0.54  fof(f107,plain,(
% 1.34/0.54    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1 | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)) )),
% 1.34/0.54    inference(superposition,[],[f73,f103])).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f72])).
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(resolution,[],[f34,f33])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f60])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f42,f52,f52,f52])).
% 1.34/0.54  fof(f42,plain,(
% 1.34/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f28])).
% 1.34/0.54  fof(f250,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f241,f207])).
% 1.34/0.54  fof(f207,plain,(
% 1.34/0.54    ( ! [X5] : (~r2_hidden(sK0,k4_xboole_0(X5,k1_xboole_0))) )),
% 1.34/0.54    inference(superposition,[],[f62,f191])).
% 1.34/0.54  fof(f241,plain,(
% 1.34/0.54    r2_hidden(sK0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.54    inference(superposition,[],[f33,f239])).
% 1.34/0.54  fof(f239,plain,(
% 1.34/0.54    sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.34/0.54    inference(subsumption_resolution,[],[f234,f208])).
% 1.34/0.54  fof(f234,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | sK0 = sK3(k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.34/0.54    inference(resolution,[],[f209,f211])).
% 1.34/0.54  fof(f211,plain,(
% 1.34/0.54    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0) | sK0 = X8) )),
% 1.34/0.54    inference(superposition,[],[f102,f191])).
% 1.34/0.54  fof(f209,plain,(
% 1.34/0.54    ( ! [X6] : (r2_hidden(sK3(k4_xboole_0(X6,k1_xboole_0)),X6) | k1_xboole_0 = k4_xboole_0(X6,k1_xboole_0)) )),
% 1.34/0.54    inference(superposition,[],[f76,f191])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (9853)------------------------------
% 1.34/0.54  % (9853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (9853)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (9853)Memory used [KB]: 6396
% 1.34/0.54  % (9853)Time elapsed: 0.111 s
% 1.34/0.54  % (9853)------------------------------
% 1.34/0.54  % (9853)------------------------------
% 1.34/0.54  % (9859)Refutation not found, incomplete strategy% (9859)------------------------------
% 1.34/0.54  % (9859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (9859)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (9859)Memory used [KB]: 10618
% 1.34/0.54  % (9859)Time elapsed: 0.125 s
% 1.34/0.54  % (9859)------------------------------
% 1.34/0.54  % (9859)------------------------------
% 1.34/0.54  % (9845)Success in time 0.182 s
%------------------------------------------------------------------------------
