%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:39 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 787 expanded)
%              Number of leaves         :   15 ( 190 expanded)
%              Depth                    :   24
%              Number of atoms          :  310 (4571 expanded)
%              Number of equality atoms :  140 (1064 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1384,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1383,f987])).

fof(f987,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f863,f887])).

fof(f887,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f876,f423])).

fof(f423,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f414,f422])).

fof(f422,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f413,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f413,plain,(
    r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f42,f373])).

fof(f373,plain,(
    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f372,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f372,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) ),
    inference(subsumption_resolution,[],[f371,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f371,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) ),
    inference(subsumption_resolution,[],[f367,f142])).

fof(f142,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_tarski(sK1))
      | ~ r2_hidden(X4,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f70,f88])).

fof(f88,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f81,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f367,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) ),
    inference(resolution,[],[f366,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f366,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK1,sK0)
      | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0) ) ),
    inference(superposition,[],[f38,f57])).

fof(f38,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f414,plain,(
    k3_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f45,f373])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f876,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f855,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f855,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f395,f45])).

fof(f395,plain,(
    ! [X0] : k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f381,f48])).

fof(f381,plain,(
    ! [X5] : r1_xboole_0(k1_tarski(sK1),k4_xboole_0(X5,sK0)) ),
    inference(resolution,[],[f376,f47])).

fof(f376,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f375,f70])).

fof(f375,plain,(
    r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f38,f373])).

fof(f863,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f42,f395])).

fof(f1383,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1382,f887])).

fof(f1382,plain,(
    ~ r1_tarski(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f1377,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1377,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(X0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1375,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f1375,plain,(
    ! [X23,X22] : ~ r1_tarski(k1_enumset1(X22,X23,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1272,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f1272,plain,(
    ! [X19,X20,X18] : ~ r1_tarski(k1_enumset1(X18,X19,sK1),k4_xboole_0(X20,sK0)) ),
    inference(resolution,[],[f1253,f73])).

fof(f73,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1253,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK1,X10)
      | ~ r1_tarski(X10,k4_xboole_0(X11,sK0)) ) ),
    inference(subsumption_resolution,[],[f1245,f388])).

fof(f388,plain,(
    ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f376,f39])).

fof(f1245,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK1,k1_xboole_0)
      | ~ r2_hidden(sK1,X10)
      | ~ r1_tarski(X10,k4_xboole_0(X11,sK0)) ) ),
    inference(superposition,[],[f380,f51])).

fof(f380,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK1,k4_xboole_0(X3,k4_xboole_0(X4,sK0)))
      | ~ r2_hidden(sK1,X3) ) ),
    inference(resolution,[],[f376,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (29824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (29832)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (29842)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (29831)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (29821)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (29843)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (29835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (29820)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (29823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (29825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (29828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (29837)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (29830)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (29848)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (29826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (29829)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (29828)Refutation not found, incomplete strategy% (29828)------------------------------
% 0.19/0.52  % (29828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (29847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (29828)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (29828)Memory used [KB]: 10618
% 0.19/0.53  % (29828)Time elapsed: 0.125 s
% 0.19/0.53  % (29828)------------------------------
% 0.19/0.53  % (29828)------------------------------
% 0.19/0.53  % (29822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (29839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (29822)Refutation not found, incomplete strategy% (29822)------------------------------
% 0.19/0.53  % (29822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (29822)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (29822)Memory used [KB]: 10746
% 0.19/0.53  % (29822)Time elapsed: 0.129 s
% 0.19/0.53  % (29822)------------------------------
% 0.19/0.53  % (29822)------------------------------
% 0.19/0.53  % (29845)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (29846)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (29840)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (29837)Refutation not found, incomplete strategy% (29837)------------------------------
% 0.19/0.54  % (29837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (29833)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.54  % (29837)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (29837)Memory used [KB]: 10618
% 0.19/0.54  % (29837)Time elapsed: 0.145 s
% 0.19/0.54  % (29837)------------------------------
% 0.19/0.54  % (29837)------------------------------
% 0.19/0.54  % (29827)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (29844)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (29834)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.54  % (29841)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (29836)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (29838)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.56  % (29849)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.79/0.61  % (29843)Refutation found. Thanks to Tanya!
% 1.79/0.61  % SZS status Theorem for theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f1384,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(subsumption_resolution,[],[f1383,f987])).
% 1.79/0.61  fof(f987,plain,(
% 1.79/0.61    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.79/0.61    inference(backward_demodulation,[],[f863,f887])).
% 1.79/0.61  fof(f887,plain,(
% 1.79/0.61    k1_xboole_0 = k1_tarski(sK1)),
% 1.79/0.61    inference(forward_demodulation,[],[f876,f423])).
% 1.79/0.61  fof(f423,plain,(
% 1.79/0.61    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(backward_demodulation,[],[f414,f422])).
% 1.79/0.61  fof(f422,plain,(
% 1.79/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.79/0.61    inference(resolution,[],[f413,f51])).
% 1.79/0.61  fof(f51,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f26])).
% 1.79/0.61  fof(f26,plain,(
% 1.79/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.79/0.61    inference(nnf_transformation,[],[f3])).
% 1.79/0.61  fof(f3,axiom,(
% 1.79/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.79/0.61  fof(f413,plain,(
% 1.79/0.61    r1_tarski(sK0,sK0)),
% 1.79/0.61    inference(superposition,[],[f42,f373])).
% 1.79/0.61  fof(f373,plain,(
% 1.79/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(subsumption_resolution,[],[f372,f57])).
% 1.79/0.61  fof(f57,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f31])).
% 1.79/0.61  fof(f31,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.79/0.61  fof(f30,plain,(
% 1.79/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f29,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.61    inference(rectify,[],[f28])).
% 1.79/0.61  fof(f28,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.61    inference(flattening,[],[f27])).
% 1.79/0.61  fof(f27,plain,(
% 1.79/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.61    inference(nnf_transformation,[],[f2])).
% 1.79/0.61  fof(f2,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.79/0.61  fof(f372,plain,(
% 1.79/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f371,f37])).
% 1.79/0.61  fof(f37,plain,(
% 1.79/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(cnf_transformation,[],[f24])).
% 1.79/0.61  fof(f24,plain,(
% 1.79/0.61    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.79/0.61  fof(f23,plain,(
% 1.79/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f22,plain,(
% 1.79/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f19])).
% 1.79/0.61  fof(f19,plain,(
% 1.79/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f18])).
% 1.79/0.61  fof(f18,negated_conjecture,(
% 1.79/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/0.61    inference(negated_conjecture,[],[f17])).
% 1.79/0.61  fof(f17,conjecture,(
% 1.79/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.79/0.61  fof(f371,plain,(
% 1.79/0.61    r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f367,f142])).
% 1.79/0.61  fof(f142,plain,(
% 1.79/0.61    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK1)) | ~r2_hidden(X4,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))) )),
% 1.79/0.61    inference(superposition,[],[f70,f88])).
% 1.79/0.61  fof(f88,plain,(
% 1.79/0.61    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(resolution,[],[f81,f48])).
% 1.79/0.61  fof(f48,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f25])).
% 1.79/0.61  fof(f25,plain,(
% 1.79/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.79/0.61    inference(nnf_transformation,[],[f10])).
% 1.79/0.61  fof(f10,axiom,(
% 1.79/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.79/0.61  fof(f81,plain,(
% 1.79/0.61    r1_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(resolution,[],[f37,f47])).
% 1.79/0.61  fof(f47,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f20])).
% 1.79/0.61  fof(f20,plain,(
% 1.79/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.79/0.61    inference(ennf_transformation,[],[f16])).
% 1.79/0.61  fof(f16,axiom,(
% 1.79/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.79/0.61  fof(f70,plain,(
% 1.79/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(equality_resolution,[],[f55])).
% 1.79/0.61  fof(f55,plain,(
% 1.79/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.61    inference(cnf_transformation,[],[f31])).
% 1.79/0.61  fof(f367,plain,(
% 1.79/0.61    r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)),
% 1.79/0.61    inference(resolution,[],[f366,f59])).
% 1.79/0.61  fof(f59,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f31])).
% 1.79/0.61  fof(f366,plain,(
% 1.79/0.61    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK1,sK0)),
% 1.79/0.61    inference(duplicate_literal_removal,[],[f365])).
% 1.79/0.61  fof(f365,plain,(
% 1.79/0.61    r2_hidden(sK1,sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)),
% 1.79/0.61    inference(equality_resolution,[],[f82])).
% 1.79/0.61  fof(f82,plain,(
% 1.79/0.61    ( ! [X0] : (sK0 != X0 | r2_hidden(sK1,sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0)) )),
% 1.79/0.61    inference(superposition,[],[f38,f57])).
% 1.79/0.61  fof(f38,plain,(
% 1.79/0.61    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f24])).
% 1.79/0.61  fof(f42,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f5])).
% 1.79/0.61  fof(f5,axiom,(
% 1.79/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.79/0.61  fof(f414,plain,(
% 1.79/0.61    k3_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,sK0)),
% 1.79/0.61    inference(superposition,[],[f45,f373])).
% 1.79/0.61  fof(f45,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f7])).
% 1.79/0.61  fof(f7,axiom,(
% 1.79/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.61  fof(f876,plain,(
% 1.79/0.61    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.79/0.61    inference(superposition,[],[f855,f43])).
% 1.79/0.61  fof(f43,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f1])).
% 1.79/0.61  fof(f1,axiom,(
% 1.79/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.61  fof(f855,plain,(
% 1.79/0.61    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK0)),
% 1.79/0.61    inference(superposition,[],[f395,f45])).
% 1.79/0.61  fof(f395,plain,(
% 1.79/0.61    ( ! [X0] : (k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k4_xboole_0(X0,sK0))) )),
% 1.79/0.61    inference(resolution,[],[f381,f48])).
% 1.79/0.61  fof(f381,plain,(
% 1.79/0.61    ( ! [X5] : (r1_xboole_0(k1_tarski(sK1),k4_xboole_0(X5,sK0))) )),
% 1.79/0.61    inference(resolution,[],[f376,f47])).
% 1.79/0.61  fof(f376,plain,(
% 1.79/0.61    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK0))) )),
% 1.79/0.61    inference(resolution,[],[f375,f70])).
% 1.79/0.61  fof(f375,plain,(
% 1.79/0.61    r2_hidden(sK1,sK0)),
% 1.79/0.61    inference(trivial_inequality_removal,[],[f374])).
% 1.79/0.61  fof(f374,plain,(
% 1.79/0.61    sK0 != sK0 | r2_hidden(sK1,sK0)),
% 1.79/0.61    inference(backward_demodulation,[],[f38,f373])).
% 1.79/0.61  fof(f863,plain,(
% 1.79/0.61    r1_tarski(k1_tarski(sK1),k1_tarski(sK1))),
% 1.79/0.61    inference(superposition,[],[f42,f395])).
% 1.79/0.61  fof(f1383,plain,(
% 1.79/0.61    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.79/0.61    inference(forward_demodulation,[],[f1382,f887])).
% 1.79/0.61  fof(f1382,plain,(
% 1.79/0.61    ~r1_tarski(k1_tarski(sK1),k1_xboole_0)),
% 1.79/0.61    inference(superposition,[],[f1377,f41])).
% 1.79/0.61  fof(f41,plain,(
% 1.79/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f12])).
% 1.79/0.61  fof(f12,axiom,(
% 1.79/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.79/0.61  fof(f1377,plain,(
% 1.79/0.61    ( ! [X0] : (~r1_tarski(k2_tarski(X0,sK1),k1_xboole_0)) )),
% 1.79/0.61    inference(superposition,[],[f1375,f44])).
% 1.79/0.61  fof(f44,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,axiom,(
% 1.79/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.61  fof(f1375,plain,(
% 1.79/0.61    ( ! [X23,X22] : (~r1_tarski(k1_enumset1(X22,X23,sK1),k1_xboole_0)) )),
% 1.79/0.61    inference(superposition,[],[f1272,f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f9])).
% 1.79/0.61  fof(f9,axiom,(
% 1.79/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.79/0.61  fof(f1272,plain,(
% 1.79/0.61    ( ! [X19,X20,X18] : (~r1_tarski(k1_enumset1(X18,X19,sK1),k4_xboole_0(X20,sK0))) )),
% 1.79/0.61    inference(resolution,[],[f1253,f73])).
% 1.79/0.61  fof(f73,plain,(
% 1.79/0.61    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.79/0.61    inference(equality_resolution,[],[f72])).
% 1.79/0.61  fof(f72,plain,(
% 1.79/0.61    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.79/0.61    inference(equality_resolution,[],[f64])).
% 1.79/0.61  fof(f64,plain,(
% 1.79/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.79/0.61    inference(cnf_transformation,[],[f36])).
% 1.79/0.61  fof(f36,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 1.79/0.61  fof(f35,plain,(
% 1.79/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f34,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(rectify,[],[f33])).
% 1.79/0.61  fof(f33,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(flattening,[],[f32])).
% 1.79/0.61  fof(f32,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/0.61    inference(nnf_transformation,[],[f21])).
% 1.79/0.61  fof(f21,plain,(
% 1.79/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.79/0.61    inference(ennf_transformation,[],[f11])).
% 1.79/0.61  fof(f11,axiom,(
% 1.79/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.79/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.79/0.61  fof(f1253,plain,(
% 1.79/0.61    ( ! [X10,X11] : (~r2_hidden(sK1,X10) | ~r1_tarski(X10,k4_xboole_0(X11,sK0))) )),
% 1.79/0.61    inference(subsumption_resolution,[],[f1245,f388])).
% 1.79/0.61  fof(f388,plain,(
% 1.79/0.61    ~r2_hidden(sK1,k1_xboole_0)),
% 1.79/0.61    inference(superposition,[],[f376,f39])).
% 1.79/0.61  fof(f1245,plain,(
% 1.79/0.61    ( ! [X10,X11] : (r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(sK1,X10) | ~r1_tarski(X10,k4_xboole_0(X11,sK0))) )),
% 1.79/0.61    inference(superposition,[],[f380,f51])).
% 1.79/0.61  fof(f380,plain,(
% 1.79/0.61    ( ! [X4,X3] : (r2_hidden(sK1,k4_xboole_0(X3,k4_xboole_0(X4,sK0))) | ~r2_hidden(sK1,X3)) )),
% 1.79/0.61    inference(resolution,[],[f376,f69])).
% 1.79/0.61  fof(f69,plain,(
% 1.79/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.79/0.61    inference(equality_resolution,[],[f56])).
% 1.79/0.61  fof(f56,plain,(
% 1.79/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.61    inference(cnf_transformation,[],[f31])).
% 1.79/0.61  % SZS output end Proof for theBenchmark
% 1.79/0.61  % (29843)------------------------------
% 1.79/0.61  % (29843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (29843)Termination reason: Refutation
% 1.79/0.61  
% 1.79/0.61  % (29843)Memory used [KB]: 2302
% 1.79/0.61  % (29843)Time elapsed: 0.153 s
% 1.79/0.61  % (29843)------------------------------
% 1.79/0.61  % (29843)------------------------------
% 1.79/0.61  % (29819)Success in time 0.26 s
%------------------------------------------------------------------------------
