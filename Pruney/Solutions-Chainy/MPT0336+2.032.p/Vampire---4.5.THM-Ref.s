%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:27 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 126 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  240 ( 409 expanded)
%              Number of equality atoms :  126 ( 163 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(subsumption_resolution,[],[f434,f62])).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f434,plain,(
    ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f431])).

fof(f431,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f429,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f429,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f424,f85])).

fof(f85,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f79,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f39,f60])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f424,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f391,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f391,plain,(
    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f351,f191])).

fof(f191,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f184,f58])).

fof(f184,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f183,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f183,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f180,f85])).

fof(f180,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f175,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f175,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f82,f58])).

fof(f82,plain,(
    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f40,f61])).

fof(f40,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f351,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f166,f118])).

fof(f118,plain,
    ( k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f63,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f37,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f166,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_xboole_0(k1_enumset1(sK3,X0,X1),sK2) ),
    inference(resolution,[],[f112,f61])).

fof(f112,plain,(
    ! [X4,X5] : ~ r1_xboole_0(k1_enumset1(sK3,X4,X5),sK2) ),
    inference(resolution,[],[f78,f73])).

fof(f73,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f78,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3,X1)
      | ~ r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f38,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:37:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.56  % (30468)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (30463)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (30482)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (30474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.58  % (30466)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.58  % (30462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.65/0.58  % (30460)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.65/0.59  % (30476)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.59  % (30464)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.65/0.60  % (30458)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.65/0.60  % (30461)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.86/0.61  % (30472)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.86/0.61  % (30473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.86/0.61  % (30481)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.86/0.61  % (30471)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.86/0.61  % (30486)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.86/0.61  % (30459)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.86/0.61  % (30477)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.86/0.62  % (30487)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.86/0.62  % (30465)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.86/0.63  % (30470)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.86/0.63  % (30480)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.86/0.63  % (30483)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.86/0.63  % (30475)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.86/0.63  % (30469)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.86/0.64  % (30484)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.86/0.64  % (30467)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.86/0.64  % (30485)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.86/0.64  % (30478)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.86/0.64  % (30479)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.86/0.65  % (30475)Refutation not found, incomplete strategy% (30475)------------------------------
% 1.86/0.65  % (30475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.65  % (30475)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.65  
% 1.86/0.65  % (30475)Memory used [KB]: 10746
% 1.86/0.65  % (30475)Time elapsed: 0.159 s
% 1.86/0.65  % (30475)------------------------------
% 1.86/0.65  % (30475)------------------------------
% 1.86/0.65  % (30458)Refutation found. Thanks to Tanya!
% 1.86/0.65  % SZS status Theorem for theBenchmark
% 1.86/0.65  % SZS output start Proof for theBenchmark
% 1.86/0.65  fof(f435,plain,(
% 1.86/0.65    $false),
% 1.86/0.65    inference(subsumption_resolution,[],[f434,f62])).
% 1.86/0.65  fof(f62,plain,(
% 1.86/0.65    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f5])).
% 1.86/0.65  fof(f5,axiom,(
% 1.86/0.65    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.86/0.65  fof(f434,plain,(
% 1.86/0.65    ~r1_xboole_0(sK0,k1_xboole_0)),
% 1.86/0.65    inference(trivial_inequality_removal,[],[f431])).
% 1.86/0.65  fof(f431,plain,(
% 1.86/0.65    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK0,k1_xboole_0)),
% 1.86/0.65    inference(superposition,[],[f429,f60])).
% 1.86/0.65  fof(f60,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f36])).
% 1.86/0.65  fof(f36,plain,(
% 1.86/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.86/0.65    inference(nnf_transformation,[],[f2])).
% 1.86/0.65  fof(f2,axiom,(
% 1.86/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.86/0.65  fof(f429,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK0,k1_xboole_0)),
% 1.86/0.65    inference(forward_demodulation,[],[f424,f85])).
% 1.86/0.65  fof(f85,plain,(
% 1.86/0.65    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.86/0.65    inference(superposition,[],[f79,f58])).
% 1.86/0.65  fof(f58,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f1])).
% 1.86/0.65  fof(f1,axiom,(
% 1.86/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.86/0.65  fof(f79,plain,(
% 1.86/0.65    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.86/0.65    inference(resolution,[],[f39,f60])).
% 1.86/0.65  fof(f39,plain,(
% 1.86/0.65    r1_xboole_0(sK2,sK1)),
% 1.86/0.65    inference(cnf_transformation,[],[f26])).
% 1.86/0.65  fof(f26,plain,(
% 1.86/0.65    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.86/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).
% 1.86/0.65  fof(f25,plain,(
% 1.86/0.65    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.86/0.65    introduced(choice_axiom,[])).
% 1.86/0.65  fof(f21,plain,(
% 1.86/0.65    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.86/0.65    inference(flattening,[],[f20])).
% 1.86/0.65  fof(f20,plain,(
% 1.86/0.65    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.86/0.65    inference(ennf_transformation,[],[f18])).
% 1.86/0.65  fof(f18,negated_conjecture,(
% 1.86/0.65    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.86/0.65    inference(negated_conjecture,[],[f17])).
% 1.86/0.65  fof(f17,conjecture,(
% 1.86/0.65    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.86/0.65  fof(f424,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.86/0.65    inference(superposition,[],[f391,f57])).
% 1.86/0.65  fof(f57,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f4])).
% 1.86/0.65  fof(f4,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.86/0.65  fof(f391,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 1.86/0.65    inference(subsumption_resolution,[],[f351,f191])).
% 1.86/0.65  fof(f191,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 1.86/0.65    inference(superposition,[],[f184,f58])).
% 1.86/0.65  fof(f184,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK1,sK0)),
% 1.86/0.65    inference(resolution,[],[f183,f61])).
% 1.86/0.65  fof(f61,plain,(
% 1.86/0.65    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.86/0.65    inference(cnf_transformation,[],[f36])).
% 1.86/0.65  fof(f183,plain,(
% 1.86/0.65    ~r1_xboole_0(sK1,sK0)),
% 1.86/0.65    inference(subsumption_resolution,[],[f180,f85])).
% 1.86/0.65  fof(f180,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.86/0.65    inference(superposition,[],[f175,f41])).
% 1.86/0.65  fof(f41,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f22])).
% 1.86/0.65  fof(f22,plain,(
% 1.86/0.65    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.86/0.65    inference(ennf_transformation,[],[f6])).
% 1.86/0.65  fof(f6,axiom,(
% 1.86/0.65    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.86/0.65  fof(f175,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.86/0.65    inference(superposition,[],[f82,f58])).
% 1.86/0.65  fof(f82,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.86/0.65    inference(resolution,[],[f40,f61])).
% 1.86/0.65  fof(f40,plain,(
% 1.86/0.65    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.86/0.65    inference(cnf_transformation,[],[f26])).
% 1.86/0.65  fof(f351,plain,(
% 1.86/0.65    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.86/0.65    inference(superposition,[],[f166,f118])).
% 1.86/0.65  fof(f118,plain,(
% 1.86/0.65    k3_xboole_0(sK0,sK1) = k1_enumset1(sK3,sK3,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.86/0.65    inference(resolution,[],[f64,f67])).
% 1.86/0.65  fof(f67,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 1.86/0.65    inference(definition_unfolding,[],[f53,f63,f63])).
% 1.86/0.65  fof(f63,plain,(
% 1.86/0.65    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.86/0.65    inference(definition_unfolding,[],[f56,f59])).
% 1.86/0.65  fof(f59,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f9])).
% 1.86/0.65  fof(f9,axiom,(
% 1.86/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.86/0.65  fof(f56,plain,(
% 1.86/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f8])).
% 1.86/0.65  fof(f8,axiom,(
% 1.86/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.86/0.65  fof(f53,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.86/0.65    inference(cnf_transformation,[],[f35])).
% 1.86/0.65  fof(f35,plain,(
% 1.86/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.86/0.65    inference(flattening,[],[f34])).
% 1.86/0.65  fof(f34,plain,(
% 1.86/0.65    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.86/0.65    inference(nnf_transformation,[],[f15])).
% 1.86/0.65  fof(f15,axiom,(
% 1.86/0.65    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.86/0.65  fof(f64,plain,(
% 1.86/0.65    r1_tarski(k3_xboole_0(sK0,sK1),k1_enumset1(sK3,sK3,sK3))),
% 1.86/0.65    inference(definition_unfolding,[],[f37,f63])).
% 1.86/0.65  fof(f37,plain,(
% 1.86/0.65    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.86/0.65    inference(cnf_transformation,[],[f26])).
% 1.86/0.65  fof(f166,plain,(
% 1.86/0.65    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(k1_enumset1(sK3,X0,X1),sK2)) )),
% 1.86/0.65    inference(resolution,[],[f112,f61])).
% 1.86/0.65  fof(f112,plain,(
% 1.86/0.65    ( ! [X4,X5] : (~r1_xboole_0(k1_enumset1(sK3,X4,X5),sK2)) )),
% 1.86/0.65    inference(resolution,[],[f78,f73])).
% 1.86/0.65  fof(f73,plain,(
% 1.86/0.65    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.86/0.65    inference(equality_resolution,[],[f72])).
% 1.86/0.65  fof(f72,plain,(
% 1.86/0.65    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.86/0.65    inference(equality_resolution,[],[f43])).
% 1.86/0.65  fof(f43,plain,(
% 1.86/0.65    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.86/0.65    inference(cnf_transformation,[],[f31])).
% 1.86/0.65  fof(f31,plain,(
% 1.86/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.86/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.86/0.65  fof(f30,plain,(
% 1.86/0.65    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.86/0.65    introduced(choice_axiom,[])).
% 1.86/0.65  fof(f29,plain,(
% 1.86/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.86/0.65    inference(rectify,[],[f28])).
% 1.86/0.65  fof(f28,plain,(
% 1.86/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.86/0.65    inference(flattening,[],[f27])).
% 1.86/0.65  fof(f27,plain,(
% 1.86/0.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.86/0.65    inference(nnf_transformation,[],[f23])).
% 1.86/0.65  fof(f23,plain,(
% 1.86/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.86/0.65    inference(ennf_transformation,[],[f7])).
% 1.86/0.65  fof(f7,axiom,(
% 1.86/0.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.86/0.65  fof(f78,plain,(
% 1.86/0.65    ( ! [X1] : (~r2_hidden(sK3,X1) | ~r1_xboole_0(X1,sK2)) )),
% 1.86/0.65    inference(resolution,[],[f38,f52])).
% 1.86/0.65  fof(f52,plain,(
% 1.86/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.86/0.65    inference(cnf_transformation,[],[f33])).
% 1.86/0.65  fof(f33,plain,(
% 1.86/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.86/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f32])).
% 1.86/0.65  fof(f32,plain,(
% 1.86/0.65    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.86/0.65    introduced(choice_axiom,[])).
% 1.86/0.65  fof(f24,plain,(
% 1.86/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.86/0.65    inference(ennf_transformation,[],[f19])).
% 1.86/0.65  fof(f19,plain,(
% 1.86/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.65    inference(rectify,[],[f3])).
% 1.86/0.65  fof(f3,axiom,(
% 1.86/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.86/0.65  fof(f38,plain,(
% 1.86/0.65    r2_hidden(sK3,sK2)),
% 1.86/0.65    inference(cnf_transformation,[],[f26])).
% 1.86/0.65  % SZS output end Proof for theBenchmark
% 1.86/0.65  % (30458)------------------------------
% 1.86/0.65  % (30458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.65  % (30458)Termination reason: Refutation
% 1.86/0.65  
% 1.86/0.65  % (30458)Memory used [KB]: 1918
% 1.86/0.65  % (30458)Time elapsed: 0.222 s
% 1.86/0.65  % (30458)------------------------------
% 1.86/0.65  % (30458)------------------------------
% 1.86/0.66  % (30457)Success in time 0.284 s
%------------------------------------------------------------------------------
