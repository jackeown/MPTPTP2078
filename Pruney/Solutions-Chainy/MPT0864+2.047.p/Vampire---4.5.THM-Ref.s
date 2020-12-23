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
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 190 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 ( 451 expanded)
%              Number of equality atoms :   97 ( 290 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f384,f127])).

fof(f127,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f32,f92])).

fof(f92,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f384,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f109,f378])).

fof(f378,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f368,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X7,X3,X1] : r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7) != X6 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(f368,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ) ),
    inference(subsumption_resolution,[],[f366,f99])).

fof(f366,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ) ),
    inference(backward_demodulation,[],[f283,f312])).

fof(f312,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f302,f127])).

fof(f302,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(superposition,[],[f109,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f293,f99])).

fof(f293,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
      | sK0 = sK1 ) ),
    inference(subsumption_resolution,[],[f288,f99])).

fof(f288,plain,(
    ! [X3] :
      ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f177,f168])).

fof(f168,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK0,X3)
      | ~ r2_hidden(sK1,X2)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f94,f123])).

fof(f123,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f25,f121])).

fof(f121,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f120,f119])).

fof(f119,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f24,f118])).

fof(f118,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f24,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f120,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f177,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k2_zfmisc_1(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))
      | k1_xboole_0 = k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4) ) ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f283,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4)
      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ) ),
    inference(resolution,[],[f176,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f94,f25])).

fof(f176,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))
      | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    ! [X4,X2,X7,X5,X3,X1] : r2_hidden(X7,k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X6)
      | k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5) != X6 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 != X7
      | r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 != X7
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (15517)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (15521)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (15534)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (15520)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (15518)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (15516)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (15545)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (15540)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (15525)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (15544)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (15519)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (15525)Refutation not found, incomplete strategy% (15525)------------------------------
% 0.20/0.52  % (15525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15531)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (15539)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (15530)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (15535)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (15529)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (15538)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (15537)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (15525)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  % (15528)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  
% 0.20/0.52  % (15525)Memory used [KB]: 10618
% 0.20/0.52  % (15525)Time elapsed: 0.117 s
% 0.20/0.52  % (15525)------------------------------
% 0.20/0.52  % (15525)------------------------------
% 0.20/0.52  % (15530)Refutation not found, incomplete strategy% (15530)------------------------------
% 0.20/0.52  % (15530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15530)Memory used [KB]: 6268
% 0.20/0.52  % (15530)Time elapsed: 0.006 s
% 0.20/0.52  % (15530)------------------------------
% 0.20/0.52  % (15530)------------------------------
% 0.20/0.53  % (15536)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (15527)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (15541)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (15533)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (15542)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (15526)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (15522)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (15543)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (15533)Refutation not found, incomplete strategy% (15533)------------------------------
% 1.29/0.53  % (15533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (15533)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (15533)Memory used [KB]: 10618
% 1.29/0.53  % (15533)Time elapsed: 0.119 s
% 1.29/0.53  % (15533)------------------------------
% 1.29/0.53  % (15533)------------------------------
% 1.29/0.53  % (15523)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (15515)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.54  % (15515)Refutation not found, incomplete strategy% (15515)------------------------------
% 1.29/0.54  % (15515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15515)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (15515)Memory used [KB]: 1663
% 1.29/0.54  % (15515)Time elapsed: 0.114 s
% 1.29/0.54  % (15515)------------------------------
% 1.29/0.54  % (15515)------------------------------
% 1.29/0.54  % (15521)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f394,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(subsumption_resolution,[],[f384,f127])).
% 1.29/0.54  fof(f127,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.54    inference(duplicate_literal_removal,[],[f126])).
% 1.29/0.54  fof(f126,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.54    inference(resolution,[],[f32,f92])).
% 1.29/0.54  fof(f92,plain,(
% 1.29/0.54    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.29/0.54    inference(equality_resolution,[],[f28])).
% 1.29/0.54  fof(f28,plain,(
% 1.29/0.54    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f20])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.29/0.54    inference(ennf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f21])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.29/0.54    inference(ennf_transformation,[],[f18])).
% 1.29/0.54  fof(f18,plain,(
% 1.29/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.54    inference(rectify,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.29/0.54  fof(f384,plain,(
% 1.29/0.54    r2_hidden(sK0,k1_xboole_0)),
% 1.29/0.54    inference(superposition,[],[f109,f378])).
% 1.29/0.54  fof(f378,plain,(
% 1.29/0.54    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.29/0.54    inference(resolution,[],[f368,f99])).
% 1.29/0.54  fof(f99,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7))) )),
% 1.29/0.54    inference(equality_resolution,[],[f98])).
% 1.29/0.54  fof(f98,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7) != X6) )),
% 1.29/0.54    inference(equality_resolution,[],[f78])).
% 1.29/0.54  fof(f78,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.29/0.54    inference(definition_unfolding,[],[f67,f68])).
% 1.29/0.54  fof(f68,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f52,f53])).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f9])).
% 1.29/0.54  fof(f9,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.29/0.54  fof(f52,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.29/0.54  fof(f67,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.29/0.54    inference(cnf_transformation,[],[f23])).
% 1.29/0.54  fof(f23,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.29/0.54    inference(ennf_transformation,[],[f14])).
% 1.29/0.54  fof(f14,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).
% 1.29/0.54  fof(f368,plain,(
% 1.29/0.54    ( ! [X4] : (~r2_hidden(sK2,X4) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )),
% 1.29/0.54    inference(subsumption_resolution,[],[f366,f99])).
% 1.29/0.54  fof(f366,plain,(
% 1.29/0.54    ( ! [X4] : (~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )),
% 1.29/0.54    inference(backward_demodulation,[],[f283,f312])).
% 1.29/0.54  fof(f312,plain,(
% 1.29/0.54    sK0 = sK1),
% 1.29/0.54    inference(subsumption_resolution,[],[f302,f127])).
% 1.29/0.54  fof(f302,plain,(
% 1.29/0.54    r2_hidden(sK0,k1_xboole_0) | sK0 = sK1),
% 1.29/0.54    inference(superposition,[],[f109,f294])).
% 1.29/0.54  fof(f294,plain,(
% 1.29/0.54    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.29/0.54    inference(resolution,[],[f293,f99])).
% 1.29/0.54  fof(f293,plain,(
% 1.29/0.54    ( ! [X3] : (~r2_hidden(sK1,X3) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = sK1) )),
% 1.29/0.54    inference(subsumption_resolution,[],[f288,f99])).
% 1.29/0.54  fof(f288,plain,(
% 1.29/0.54    ( ! [X3] : (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 1.29/0.54    inference(resolution,[],[f177,f168])).
% 1.29/0.54  fof(f168,plain,(
% 1.29/0.54    ( ! [X2,X3] : (r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK0,X3) | ~r2_hidden(sK1,X2) | sK0 = sK1) )),
% 1.29/0.54    inference(superposition,[],[f94,f123])).
% 1.29/0.54  fof(f123,plain,(
% 1.29/0.54    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 1.29/0.54    inference(superposition,[],[f25,f121])).
% 1.29/0.54  fof(f121,plain,(
% 1.29/0.54    sK0 = sK2 | sK0 = sK1),
% 1.29/0.54    inference(superposition,[],[f120,f119])).
% 1.29/0.54  fof(f119,plain,(
% 1.29/0.54    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.29/0.54    inference(backward_demodulation,[],[f24,f118])).
% 1.29/0.54  fof(f118,plain,(
% 1.29/0.54    sK1 = k1_mcart_1(sK0)),
% 1.29/0.54    inference(superposition,[],[f30,f25])).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f15])).
% 1.29/0.54  fof(f15,axiom,(
% 1.29/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.29/0.54  fof(f24,plain,(
% 1.29/0.54    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 1.29/0.54    inference(cnf_transformation,[],[f19])).
% 1.29/0.54  fof(f19,plain,(
% 1.29/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.29/0.54    inference(ennf_transformation,[],[f17])).
% 1.29/0.54  fof(f17,negated_conjecture,(
% 1.29/0.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.29/0.54    inference(negated_conjecture,[],[f16])).
% 1.29/0.54  fof(f16,conjecture,(
% 1.29/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.29/0.54  fof(f120,plain,(
% 1.29/0.54    sK2 = k2_mcart_1(sK0)),
% 1.29/0.54    inference(superposition,[],[f31,f25])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.29/0.54    inference(cnf_transformation,[],[f15])).
% 1.29/0.54  fof(f25,plain,(
% 1.29/0.54    sK0 = k4_tarski(sK1,sK2)),
% 1.29/0.54    inference(cnf_transformation,[],[f19])).
% 1.29/0.54  fof(f94,plain,(
% 1.29/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.29/0.54    inference(equality_resolution,[],[f93])).
% 1.29/0.54  fof(f93,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.29/0.54    inference(equality_resolution,[],[f49])).
% 1.29/0.54  fof(f49,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.29/0.54    inference(cnf_transformation,[],[f10])).
% 1.29/0.54  fof(f10,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.29/0.54  fof(f177,plain,(
% 1.29/0.54    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4))) | k1_xboole_0 = k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)) )),
% 1.29/0.54    inference(resolution,[],[f75,f36])).
% 1.29/0.54  fof(f36,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.29/0.54    inference(ennf_transformation,[],[f12])).
% 1.29/0.54  fof(f12,axiom,(
% 1.29/0.54    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.29/0.54  fof(f75,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f37,f73])).
% 1.29/0.54  fof(f73,plain,(
% 1.29/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f26,f72])).
% 1.29/0.54  fof(f72,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f29,f71])).
% 1.29/0.54  fof(f71,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f39,f70])).
% 1.29/0.54  fof(f70,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f50,f69])).
% 1.29/0.54  fof(f69,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f51,f68])).
% 1.29/0.54  fof(f51,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f7])).
% 1.29/0.54  fof(f7,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.29/0.54  fof(f50,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f6])).
% 1.29/0.54  fof(f6,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.29/0.54  fof(f39,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f5])).
% 1.29/0.54  fof(f5,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.54  fof(f29,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.54  fof(f26,plain,(
% 1.29/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,axiom,(
% 1.29/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.29/0.54  fof(f283,plain,(
% 1.29/0.54    ( ! [X4] : (~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )),
% 1.29/0.54    inference(resolution,[],[f176,f167])).
% 1.29/0.54  fof(f167,plain,(
% 1.29/0.54    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK1,X0)) )),
% 1.29/0.54    inference(superposition,[],[f94,f25])).
% 1.29/0.54  fof(f176,plain,(
% 1.29/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 1.29/0.54    inference(resolution,[],[f75,f35])).
% 1.29/0.54  fof(f35,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f22])).
% 1.29/0.54  fof(f109,plain,(
% 1.29/0.54    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5))) )),
% 1.29/0.54    inference(equality_resolution,[],[f108])).
% 1.29/0.54  fof(f108,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X6) | k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5) != X6) )),
% 1.29/0.54    inference(equality_resolution,[],[f83])).
% 1.29/0.54  fof(f83,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 != X7 | r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.29/0.54    inference(definition_unfolding,[],[f62,f68])).
% 1.29/0.54  fof(f62,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 != X7 | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.29/0.54    inference(cnf_transformation,[],[f23])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (15521)------------------------------
% 1.29/0.54  % (15521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15521)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (15521)Memory used [KB]: 6780
% 1.29/0.54  % (15521)Time elapsed: 0.134 s
% 1.29/0.54  % (15521)------------------------------
% 1.29/0.54  % (15521)------------------------------
% 1.29/0.54  % (15524)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (15524)Refutation not found, incomplete strategy% (15524)------------------------------
% 1.29/0.54  % (15524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (15524)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (15524)Memory used [KB]: 10618
% 1.29/0.54  % (15524)Time elapsed: 0.140 s
% 1.29/0.54  % (15524)------------------------------
% 1.29/0.54  % (15524)------------------------------
% 1.44/0.55  % (15511)Success in time 0.19 s
%------------------------------------------------------------------------------
