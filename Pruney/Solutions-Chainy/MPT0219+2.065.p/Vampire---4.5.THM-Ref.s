%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:29 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   91 (3051 expanded)
%              Number of leaves         :   18 (1064 expanded)
%              Depth                    :   20
%              Number of atoms          :  212 (3442 expanded)
%              Number of equality atoms :  161 (3348 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f662,f42])).

fof(f42,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f662,plain,(
    sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f658])).

fof(f658,plain,
    ( sK1 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f638,f323])).

fof(f323,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k4_enumset1(X1,sK1,sK1,sK1,sK1,sK1))
      | sK1 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | sK1 = X2
      | ~ r2_hidden(X2,k4_enumset1(X1,sK1,sK1,sK1,sK1,sK1))
      | sK1 = X2 ) ),
    inference(resolution,[],[f308,f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f308,plain,(
    ! [X50] : sP0(sK1,X50,sK1,k4_enumset1(X50,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f95,f250])).

fof(f250,plain,(
    ! [X4] : k4_enumset1(X4,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,X4,sK1) ),
    inference(superposition,[],[f170,f169])).

fof(f169,plain,(
    ! [X0] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,sK1,sK1,sK1,sK1)) = k4_enumset1(X0,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f110,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6)) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)) ),
    inference(definition_unfolding,[],[f43,f70,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f110,plain,(
    ! [X2,X1] : k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f107,f96])).

fof(f96,plain,(
    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK2,sK2,sK2,sK2) ),
    inference(superposition,[],[f78,f77])).

fof(f78,plain,(
    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f41,f75,f75,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X2,X1] : k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,sK1),k4_enumset1(sK1,sK1,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f85,f101])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(k4_enumset1(X0,X0,X0,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(X0,X0,sK1,sK1,sK1,sK1) ),
    inference(forward_demodulation,[],[f98,f77])).

fof(f98,plain,(
    ! [X0] : k2_xboole_0(k4_enumset1(X0,X0,X0,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f79,f78])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f45,f71,f75,f72])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f55,f76,f73])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f44,f75,f71])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f170,plain,(
    ! [X1] : k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1)) = k4_enumset1(sK1,sK1,sK1,sK1,X1,sK1) ),
    inference(superposition,[],[f110,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X2,X2,X2,X2,X2,X0)) ),
    inference(definition_unfolding,[],[f67,f73,f74,f74])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f26,f27])).

fof(f26,plain,(
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

fof(f638,plain,(
    r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f373,f616])).

fof(f616,plain,(
    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f615,f77])).

fof(f615,plain,(
    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f614,f77])).

fof(f614,plain,(
    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1)) ),
    inference(forward_demodulation,[],[f613,f250])).

fof(f613,plain,(
    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f558,f198])).

fof(f198,plain,(
    ! [X3] : k4_enumset1(X3,X3,sK1,sK1,sK1,sK1) = k4_enumset1(X3,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f169,f142])).

fof(f142,plain,(
    ! [X0] : k4_enumset1(X0,X0,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f108,f101])).

fof(f108,plain,(
    ! [X4,X3] : k2_xboole_0(k4_enumset1(X4,X4,X3,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X3,X3,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f84,f101])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f51,f76,f69,f70])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f558,plain,(
    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f165,f96])).

fof(f165,plain,(
    ! [X6,X5] : k2_xboole_0(k4_enumset1(X6,X6,X5,X5,X5,X5),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_enumset1(X5,X5,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f157,f103])).

fof(f103,plain,(
    ! [X2] : k4_enumset1(X2,X2,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(X2,X2,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(forward_demodulation,[],[f100,f77])).

fof(f100,plain,(
    ! [X2] : k2_xboole_0(k4_enumset1(X2,X2,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f84,f78])).

fof(f157,plain,(
    ! [X6,X5] : k2_xboole_0(k4_enumset1(X6,X6,X5,X5,X5,X5),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k2_xboole_0(k4_enumset1(X5,X5,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[],[f84,f108])).

fof(f373,plain,(
    ! [X0] : r2_hidden(X0,k4_enumset1(sK1,sK1,sK1,sK1,X0,sK1)) ),
    inference(superposition,[],[f319,f250])).

fof(f319,plain,(
    ! [X4] : r2_hidden(X4,k4_enumset1(X4,sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f308,f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3] :
      ( ~ sP0(X0,X5,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (4005)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.48  % (4022)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (4022)Refutation not found, incomplete strategy% (4022)------------------------------
% 0.21/0.50  % (4022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4022)Memory used [KB]: 6140
% 0.21/0.50  % (4022)Time elapsed: 0.076 s
% 0.21/0.50  % (4022)------------------------------
% 0.21/0.50  % (4022)------------------------------
% 1.12/0.51  % (3996)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.12/0.52  % (4012)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.12/0.52  % (4012)Refutation not found, incomplete strategy% (4012)------------------------------
% 1.12/0.52  % (4012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.52  % (4012)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.52  
% 1.12/0.52  % (4012)Memory used [KB]: 10618
% 1.12/0.52  % (4012)Time elapsed: 0.116 s
% 1.12/0.52  % (4012)------------------------------
% 1.12/0.52  % (4012)------------------------------
% 1.12/0.52  % (3998)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.12/0.52  % (4004)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.12/0.52  % (4003)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.53  % (4026)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.53  % (4026)Refutation not found, incomplete strategy% (4026)------------------------------
% 1.28/0.53  % (4026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (4026)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (4026)Memory used [KB]: 1663
% 1.28/0.53  % (4026)Time elapsed: 0.001 s
% 1.28/0.53  % (4026)------------------------------
% 1.28/0.53  % (4026)------------------------------
% 1.28/0.53  % (4019)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.54  % (4009)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.54  % (4025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.54  % (3997)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.54  % (4023)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (4023)Refutation not found, incomplete strategy% (4023)------------------------------
% 1.28/0.54  % (4023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (4023)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (4023)Memory used [KB]: 6140
% 1.28/0.54  % (4023)Time elapsed: 0.129 s
% 1.28/0.54  % (4023)------------------------------
% 1.28/0.54  % (4023)------------------------------
% 1.28/0.54  % (3994)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.55  % (4002)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.55  % (3995)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.55  % (3995)Refutation not found, incomplete strategy% (3995)------------------------------
% 1.28/0.55  % (3995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (3995)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (3995)Memory used [KB]: 1663
% 1.28/0.55  % (3995)Time elapsed: 0.135 s
% 1.28/0.55  % (3995)------------------------------
% 1.28/0.55  % (3995)------------------------------
% 1.28/0.55  % (4015)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.28/0.55  % (4017)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.28/0.55  % (4015)Refutation not found, incomplete strategy% (4015)------------------------------
% 1.28/0.55  % (4015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4006)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.55  % (4015)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4015)Memory used [KB]: 1663
% 1.28/0.55  % (4015)Time elapsed: 0.140 s
% 1.28/0.55  % (4015)------------------------------
% 1.28/0.55  % (4015)------------------------------
% 1.28/0.55  % (3999)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.55  % (4006)Refutation not found, incomplete strategy% (4006)------------------------------
% 1.28/0.55  % (4006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4006)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4006)Memory used [KB]: 10618
% 1.28/0.55  % (4006)Time elapsed: 0.150 s
% 1.28/0.55  % (4006)------------------------------
% 1.28/0.55  % (4006)------------------------------
% 1.28/0.55  % (4021)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.55  % (4018)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.56  % (4013)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.56  % (4001)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.56  % (4011)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.56  % (4024)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.56  % (4020)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.56  % (4000)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.56  % (4010)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.57  % (4016)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.59  % (4024)Refutation not found, incomplete strategy% (4024)------------------------------
% 1.28/0.59  % (4024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.59  % (4024)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.59  
% 1.28/0.59  % (4024)Memory used [KB]: 6140
% 1.28/0.59  % (4024)Time elapsed: 0.179 s
% 1.28/0.59  % (4024)------------------------------
% 1.28/0.59  % (4024)------------------------------
% 1.28/0.59  % (4033)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.89/0.63  % (4034)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.89/0.64  % (4021)Refutation found. Thanks to Tanya!
% 1.89/0.64  % SZS status Theorem for theBenchmark
% 1.89/0.64  % SZS output start Proof for theBenchmark
% 1.89/0.64  fof(f663,plain,(
% 1.89/0.64    $false),
% 1.89/0.64    inference(subsumption_resolution,[],[f662,f42])).
% 1.89/0.64  fof(f42,plain,(
% 1.89/0.64    sK1 != sK2),
% 1.89/0.64    inference(cnf_transformation,[],[f30])).
% 1.89/0.64  fof(f30,plain,(
% 1.89/0.64    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.89/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f29])).
% 1.89/0.64  fof(f29,plain,(
% 1.89/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f25,plain,(
% 1.89/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.89/0.64    inference(ennf_transformation,[],[f24])).
% 1.89/0.64  fof(f24,negated_conjecture,(
% 1.89/0.64    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.89/0.64    inference(negated_conjecture,[],[f23])).
% 1.89/0.64  fof(f23,conjecture,(
% 1.89/0.64    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.89/0.64  fof(f662,plain,(
% 1.89/0.64    sK1 = sK2),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f658])).
% 1.89/0.64  fof(f658,plain,(
% 1.89/0.64    sK1 = sK2 | sK1 = sK2),
% 1.89/0.64    inference(resolution,[],[f638,f323])).
% 1.89/0.64  fof(f323,plain,(
% 1.89/0.64    ( ! [X2,X1] : (~r2_hidden(X2,k4_enumset1(X1,sK1,sK1,sK1,sK1,sK1)) | sK1 = X2 | X1 = X2) )),
% 1.89/0.64    inference(duplicate_literal_removal,[],[f317])).
% 1.89/0.64  fof(f317,plain,(
% 1.89/0.64    ( ! [X2,X1] : (X1 = X2 | sK1 = X2 | ~r2_hidden(X2,k4_enumset1(X1,sK1,sK1,sK1,sK1,sK1)) | sK1 = X2) )),
% 1.89/0.64    inference(resolution,[],[f308,f57])).
% 1.89/0.64  fof(f57,plain,(
% 1.89/0.64    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.89/0.64    inference(cnf_transformation,[],[f39])).
% 1.89/0.64  fof(f39,plain,(
% 1.89/0.64    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.89/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.89/0.64  fof(f38,plain,(
% 1.89/0.64    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f37,plain,(
% 1.89/0.64    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.89/0.64    inference(rectify,[],[f36])).
% 1.89/0.64  fof(f36,plain,(
% 1.89/0.64    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.89/0.64    inference(flattening,[],[f35])).
% 1.89/0.64  fof(f35,plain,(
% 1.89/0.64    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.89/0.64    inference(nnf_transformation,[],[f27])).
% 1.89/0.64  fof(f27,plain,(
% 1.89/0.64    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.89/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.89/0.64  fof(f308,plain,(
% 1.89/0.64    ( ! [X50] : (sP0(sK1,X50,sK1,k4_enumset1(X50,sK1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f95,f250])).
% 1.89/0.64  fof(f250,plain,(
% 1.89/0.64    ( ! [X4] : (k4_enumset1(X4,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,X4,sK1)) )),
% 1.89/0.64    inference(superposition,[],[f170,f169])).
% 1.89/0.64  fof(f169,plain,(
% 1.89/0.64    ( ! [X0] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,sK1,sK1,sK1,sK1)) = k4_enumset1(X0,sK1,sK1,sK1,sK1,sK1)) )),
% 1.89/0.64    inference(superposition,[],[f110,f77])).
% 1.89/0.64  fof(f77,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X2,X2,X2,X3,X4,X5))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f56,f72])).
% 1.89/0.64  fof(f72,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X4,X5,X6))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f54,f71])).
% 1.89/0.64  fof(f71,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f43,f70,f70])).
% 1.89/0.64  fof(f70,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f52,f69])).
% 1.89/0.64  fof(f69,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f20])).
% 1.89/0.64  fof(f20,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.89/0.64  fof(f52,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f19])).
% 1.89/0.64  fof(f19,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.89/0.64  fof(f43,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f10])).
% 1.89/0.64  fof(f10,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 1.89/0.64  fof(f54,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f22])).
% 1.89/0.64  fof(f22,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.89/0.64  fof(f56,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f21])).
% 1.89/0.64  fof(f21,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.89/0.64  fof(f110,plain,(
% 1.89/0.64    ( ! [X2,X1] : (k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(forward_demodulation,[],[f107,f96])).
% 1.89/0.64  fof(f96,plain,(
% 1.89/0.64    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK2,sK2,sK2,sK2)),
% 1.89/0.64    inference(superposition,[],[f78,f77])).
% 1.89/0.64  fof(f78,plain,(
% 1.89/0.64    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.89/0.64    inference(definition_unfolding,[],[f41,f75,f75,f75])).
% 1.89/0.64  fof(f75,plain,(
% 1.89/0.64    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f50,f74])).
% 1.89/0.64  fof(f74,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f68,f73])).
% 1.89/0.64  fof(f73,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f53,f70])).
% 1.89/0.64  fof(f53,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f18])).
% 1.89/0.64  fof(f18,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.89/0.64  fof(f68,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f17])).
% 1.89/0.64  fof(f17,axiom,(
% 1.89/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.89/0.64  fof(f50,plain,(
% 1.89/0.64    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f16])).
% 1.89/0.64  fof(f16,axiom,(
% 1.89/0.64    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.89/0.64  fof(f41,plain,(
% 1.89/0.64    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.89/0.64    inference(cnf_transformation,[],[f30])).
% 1.89/0.64  fof(f107,plain,(
% 1.89/0.64    ( ! [X2,X1] : (k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,sK1),k4_enumset1(sK1,sK1,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f85,f101])).
% 1.89/0.64  fof(f101,plain,(
% 1.89/0.64    ( ! [X0] : (k2_xboole_0(k4_enumset1(X0,X0,X0,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(X0,X0,sK1,sK1,sK1,sK1)) )),
% 1.89/0.64    inference(forward_demodulation,[],[f98,f77])).
% 1.89/0.64  fof(f98,plain,(
% 1.89/0.64    ( ! [X0] : (k2_xboole_0(k4_enumset1(X0,X0,X0,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f79,f78])).
% 1.89/0.64  fof(f79,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X3),k4_enumset1(X4,X4,X4,X5,X6,X7)))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f45,f71,f75,f72])).
% 1.89/0.64  fof(f45,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f15])).
% 1.89/0.64  fof(f15,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 1.89/0.64  fof(f85,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f55,f76,f73])).
% 1.89/0.64  fof(f76,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8)))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f44,f75,f71])).
% 1.89/0.64  fof(f44,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f11])).
% 1.89/0.64  fof(f11,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 1.89/0.64  fof(f55,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f12])).
% 1.89/0.64  fof(f12,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 1.89/0.64  fof(f170,plain,(
% 1.89/0.64    ( ! [X1] : (k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,sK1,sK1,sK1,sK1)) = k4_enumset1(sK1,sK1,sK1,sK1,X1,sK1)) )),
% 1.89/0.64    inference(superposition,[],[f110,f88])).
% 1.89/0.64  fof(f88,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X0),k4_enumset1(X2,X2,X2,X2,X2,X0))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f67,f73,f74,f74])).
% 1.89/0.64  fof(f67,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f14])).
% 1.89/0.64  fof(f14,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.89/0.64  fof(f95,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k4_enumset1(X0,X0,X0,X0,X1,X2))) )),
% 1.89/0.64    inference(equality_resolution,[],[f87])).
% 1.89/0.64  fof(f87,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 1.89/0.64    inference(definition_unfolding,[],[f65,f73])).
% 1.89/0.64  fof(f65,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.89/0.64    inference(cnf_transformation,[],[f40])).
% 1.89/0.64  fof(f40,plain,(
% 1.89/0.64    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.89/0.64    inference(nnf_transformation,[],[f28])).
% 1.89/0.64  fof(f28,plain,(
% 1.89/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.89/0.64    inference(definition_folding,[],[f26,f27])).
% 1.89/0.64  fof(f26,plain,(
% 1.89/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.89/0.64    inference(ennf_transformation,[],[f8])).
% 1.89/0.64  fof(f8,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.89/0.64  fof(f638,plain,(
% 1.89/0.64    r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.89/0.64    inference(superposition,[],[f373,f616])).
% 1.89/0.64  fof(f616,plain,(
% 1.89/0.64    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1)),
% 1.89/0.64    inference(forward_demodulation,[],[f615,f77])).
% 1.89/0.64  fof(f615,plain,(
% 1.89/0.64    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1)),
% 1.89/0.64    inference(forward_demodulation,[],[f614,f77])).
% 1.89/0.64  fof(f614,plain,(
% 1.89/0.64    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK1))),
% 1.89/0.64    inference(forward_demodulation,[],[f613,f250])).
% 1.89/0.64  fof(f613,plain,(
% 1.89/0.64    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK1,sK1,sK1,sK1,sK1))),
% 1.89/0.64    inference(forward_demodulation,[],[f558,f198])).
% 1.89/0.64  fof(f198,plain,(
% 1.89/0.64    ( ! [X3] : (k4_enumset1(X3,X3,sK1,sK1,sK1,sK1) = k4_enumset1(X3,sK1,sK1,sK1,sK1,sK1)) )),
% 1.89/0.64    inference(superposition,[],[f169,f142])).
% 1.89/0.64  fof(f142,plain,(
% 1.89/0.64    ( ! [X0] : (k4_enumset1(X0,X0,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f108,f101])).
% 1.89/0.64  fof(f108,plain,(
% 1.89/0.64    ( ! [X4,X3] : (k2_xboole_0(k4_enumset1(X4,X4,X3,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X3,X3,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f84,f101])).
% 1.89/0.64  fof(f84,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X6,X7,X8))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f51,f76,f69,f70])).
% 1.89/0.64  fof(f51,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f13])).
% 1.89/0.64  fof(f13,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 1.89/0.64  fof(f558,plain,(
% 1.89/0.64    k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK1,sK1,sK1,sK1))),
% 1.89/0.64    inference(superposition,[],[f165,f96])).
% 1.89/0.64  fof(f165,plain,(
% 1.89/0.64    ( ! [X6,X5] : (k2_xboole_0(k4_enumset1(X6,X6,X5,X5,X5,X5),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_enumset1(X5,X5,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(forward_demodulation,[],[f157,f103])).
% 1.89/0.64  fof(f103,plain,(
% 1.89/0.64    ( ! [X2] : (k4_enumset1(X2,X2,sK1,sK1,sK1,sK1) = k2_xboole_0(k4_enumset1(X2,X2,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) )),
% 1.89/0.64    inference(forward_demodulation,[],[f100,f77])).
% 1.89/0.64  fof(f100,plain,(
% 1.89/0.64    ( ! [X2] : (k2_xboole_0(k4_enumset1(X2,X2,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k2_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f84,f78])).
% 1.89/0.64  fof(f157,plain,(
% 1.89/0.64    ( ! [X6,X5] : (k2_xboole_0(k4_enumset1(X6,X6,X5,X5,X5,X5),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k2_xboole_0(k4_enumset1(X5,X5,sK1,sK1,sK1,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 1.89/0.64    inference(superposition,[],[f84,f108])).
% 1.89/0.64  fof(f373,plain,(
% 1.89/0.64    ( ! [X0] : (r2_hidden(X0,k4_enumset1(sK1,sK1,sK1,sK1,X0,sK1))) )),
% 1.89/0.64    inference(superposition,[],[f319,f250])).
% 1.89/0.64  fof(f319,plain,(
% 1.89/0.64    ( ! [X4] : (r2_hidden(X4,k4_enumset1(X4,sK1,sK1,sK1,sK1,sK1))) )),
% 1.89/0.64    inference(resolution,[],[f308,f93])).
% 1.89/0.64  fof(f93,plain,(
% 1.89/0.64    ( ! [X2,X0,X5,X3] : (~sP0(X0,X5,X2,X3) | r2_hidden(X5,X3)) )),
% 1.89/0.64    inference(equality_resolution,[],[f59])).
% 1.89/0.64  fof(f59,plain,(
% 1.89/0.64    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f39])).
% 1.89/0.64  % SZS output end Proof for theBenchmark
% 1.89/0.64  % (4021)------------------------------
% 1.89/0.64  % (4021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (4021)Termination reason: Refutation
% 1.89/0.64  
% 1.89/0.64  % (4021)Memory used [KB]: 11257
% 1.89/0.64  % (4021)Time elapsed: 0.221 s
% 1.89/0.64  % (4021)------------------------------
% 1.89/0.64  % (4021)------------------------------
% 1.89/0.64  % (3992)Success in time 0.277 s
%------------------------------------------------------------------------------
