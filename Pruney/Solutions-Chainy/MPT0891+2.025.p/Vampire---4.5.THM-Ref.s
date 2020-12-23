%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  100 (1012 expanded)
%              Number of leaves         :   15 ( 333 expanded)
%              Depth                    :   26
%              Number of atoms          :  332 (5233 expanded)
%              Number of equality atoms :  257 (4223 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(equality_resolution,[],[f363])).

fof(f363,plain,(
    ! [X1] : sK3 != X1 ),
    inference(subsumption_resolution,[],[f355,f76])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f355,plain,(
    ! [X1] :
      ( r2_hidden(sK3,k1_xboole_0)
      | sK3 != X1 ) ),
    inference(superposition,[],[f70,f332])).

fof(f332,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_enumset1(X0,X0,sK3)
      | sK3 != X0 ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X0] :
      ( sK3 != X0
      | k1_xboole_0 = k1_enumset1(X0,X0,sK3)
      | sK3 != X0 ) ),
    inference(forward_demodulation,[],[f325,f310])).

fof(f310,plain,(
    sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f161,f308])).

fof(f308,plain,(
    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,
    ( sK3 != sK3
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f303,f171])).

fof(f171,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f164,f120])).

fof(f120,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f74,f111])).

fof(f111,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f110,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f105,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f64,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f47,f46])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f74,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f65,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f65,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f164,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f33,f160])).

fof(f160,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f42,f118])).

fof(f118,plain,(
    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) = k1_mcart_1(sK3) ),
    inference(superposition,[],[f41,f111])).

fof(f41,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f303,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(equality_resolution,[],[f295])).

fof(f295,plain,(
    ! [X1] :
      ( k2_mcart_1(k1_mcart_1(sK3)) != X1
      | sK3 != X1 ) ),
    inference(subsumption_resolution,[],[f285,f76])).

fof(f285,plain,(
    ! [X1] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_xboole_0)
      | sK3 != X1
      | k2_mcart_1(k1_mcart_1(sK3)) != X1 ) ),
    inference(superposition,[],[f70,f279])).

fof(f279,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3)))
      | sK3 != X0
      | k2_mcart_1(k1_mcart_1(sK3)) != X0 ) ),
    inference(superposition,[],[f172,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK4(k1_enumset1(X0,X0,X1)) = X0
      | X0 != X1 ) ),
    inference(equality_factoring,[],[f87])).

fof(f87,plain,(
    ! [X4,X3] :
      ( sK4(k1_enumset1(X3,X3,X4)) = X4
      | sK4(k1_enumset1(X3,X3,X4)) = X3 ) ),
    inference(subsumption_resolution,[],[f85,f76])).

fof(f85,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | sK4(k1_enumset1(X3,X3,X4)) = X4
      | sK4(k1_enumset1(X3,X3,X4)) = X3 ) ),
    inference(superposition,[],[f72,f83])).

fof(f83,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k1_enumset1(X4,X4,X5)
      | sK4(k1_enumset1(X4,X4,X5)) = X5
      | sK4(k1_enumset1(X4,X4,X5)) = X4 ) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f72,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f172,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3))))
      | k1_xboole_0 = k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3))) ) ),
    inference(forward_demodulation,[],[f168,f160])).

fof(f168,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3))))
      | k1_xboole_0 = k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3)) ) ),
    inference(backward_demodulation,[],[f155,f160])).

fof(f155,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3)))
      | k1_xboole_0 = k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f114,f70])).

fof(f114,plain,(
    ! [X1] :
      ( ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),X1)
      | sK3 != sK4(X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f56,f111])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f38,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f161,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f41,f118])).

fof(f325,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_enumset1(X0,X0,sK3)
      | sK3 != X0
      | k1_mcart_1(k1_mcart_1(sK3)) != X0 ) ),
    inference(backward_demodulation,[],[f299,f310])).

fof(f299,plain,(
    ! [X0] :
      ( sK3 != X0
      | k1_xboole_0 = k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3)))
      | k1_mcart_1(k1_mcart_1(sK3)) != X0 ) ),
    inference(superposition,[],[f181,f98])).

fof(f181,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3))))
      | k1_xboole_0 = k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3))) ) ),
    inference(forward_demodulation,[],[f176,f161])).

fof(f176,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3))))
      | k1_xboole_0 = k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3)) ) ),
    inference(backward_demodulation,[],[f153,f161])).

fof(f153,plain,(
    ! [X0] :
      ( sK3 != sK4(k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3)))
      | k1_xboole_0 = k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f113,f70])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0)
      | sK3 != sK4(X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f57,f111])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f37,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26584)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (26597)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (26590)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (26591)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (26597)Refutation not found, incomplete strategy% (26597)------------------------------
% 0.20/0.52  % (26597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26581)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26588)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (26582)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (26582)Refutation not found, incomplete strategy% (26582)------------------------------
% 0.20/0.52  % (26582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26597)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26597)Memory used [KB]: 10618
% 0.20/0.53  % (26597)Time elapsed: 0.110 s
% 0.20/0.53  % (26597)------------------------------
% 0.20/0.53  % (26597)------------------------------
% 0.20/0.53  % (26606)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (26598)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (26583)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (26607)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (26593)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (26582)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26582)Memory used [KB]: 1791
% 0.20/0.53  % (26585)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (26582)Time elapsed: 0.102 s
% 0.20/0.53  % (26582)------------------------------
% 0.20/0.53  % (26582)------------------------------
% 0.20/0.53  % (26603)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (26607)Refutation not found, incomplete strategy% (26607)------------------------------
% 0.20/0.54  % (26607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26607)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26604)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (26607)Memory used [KB]: 6268
% 0.20/0.54  % (26607)Time elapsed: 0.118 s
% 0.20/0.54  % (26607)------------------------------
% 0.20/0.54  % (26607)------------------------------
% 0.20/0.54  % (26595)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (26599)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (26595)Refutation not found, incomplete strategy% (26595)------------------------------
% 0.20/0.54  % (26595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26599)Refutation not found, incomplete strategy% (26599)------------------------------
% 0.20/0.54  % (26599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26599)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26599)Memory used [KB]: 1791
% 0.20/0.54  % (26599)Time elapsed: 0.121 s
% 0.20/0.54  % (26599)------------------------------
% 0.20/0.54  % (26599)------------------------------
% 0.20/0.54  % (26598)Refutation not found, incomplete strategy% (26598)------------------------------
% 0.20/0.54  % (26598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26591)Refutation not found, incomplete strategy% (26591)------------------------------
% 0.20/0.54  % (26591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26591)Memory used [KB]: 10874
% 0.20/0.54  % (26591)Time elapsed: 0.130 s
% 0.20/0.54  % (26591)------------------------------
% 0.20/0.54  % (26591)------------------------------
% 0.20/0.54  % (26596)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (26608)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (26600)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (26589)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (26595)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26595)Memory used [KB]: 1791
% 0.20/0.55  % (26595)Time elapsed: 0.119 s
% 0.20/0.55  % (26595)------------------------------
% 0.20/0.55  % (26595)------------------------------
% 0.20/0.55  % (26608)Refutation not found, incomplete strategy% (26608)------------------------------
% 0.20/0.55  % (26608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26608)Memory used [KB]: 6268
% 0.20/0.55  % (26608)Time elapsed: 0.140 s
% 0.20/0.55  % (26608)------------------------------
% 0.20/0.55  % (26608)------------------------------
% 0.20/0.55  % (26598)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26598)Memory used [KB]: 1791
% 0.20/0.55  % (26598)Time elapsed: 0.121 s
% 0.20/0.55  % (26598)------------------------------
% 0.20/0.55  % (26598)------------------------------
% 0.20/0.55  % (26586)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.55  % (26593)Refutation not found, incomplete strategy% (26593)------------------------------
% 0.20/0.55  % (26593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26593)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26593)Memory used [KB]: 10618
% 0.20/0.55  % (26593)Time elapsed: 0.128 s
% 0.20/0.55  % (26593)------------------------------
% 0.20/0.55  % (26593)------------------------------
% 0.20/0.56  % (26601)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (26610)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (26610)Refutation not found, incomplete strategy% (26610)------------------------------
% 0.20/0.56  % (26610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (26610)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (26610)Memory used [KB]: 1663
% 0.20/0.56  % (26610)Time elapsed: 0.001 s
% 0.20/0.56  % (26610)------------------------------
% 0.20/0.56  % (26610)------------------------------
% 0.20/0.56  % (26602)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (26605)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.57  % (26605)Refutation not found, incomplete strategy% (26605)------------------------------
% 0.20/0.57  % (26605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (26605)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (26605)Memory used [KB]: 10746
% 0.20/0.57  % (26605)Time elapsed: 0.160 s
% 0.20/0.57  % (26605)------------------------------
% 0.20/0.57  % (26605)------------------------------
% 0.20/0.57  % (26609)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.68/0.57  % (26594)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.68/0.57  % (26609)Refutation not found, incomplete strategy% (26609)------------------------------
% 1.68/0.57  % (26609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.57  % (26609)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.57  
% 1.68/0.57  % (26609)Memory used [KB]: 10874
% 1.68/0.57  % (26609)Time elapsed: 0.166 s
% 1.68/0.57  % (26609)------------------------------
% 1.68/0.57  % (26609)------------------------------
% 1.68/0.58  % (26592)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.68/0.58  % (26603)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.58  % (26587)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.68/0.58  % SZS output start Proof for theBenchmark
% 1.68/0.58  fof(f385,plain,(
% 1.68/0.58    $false),
% 1.68/0.58    inference(equality_resolution,[],[f363])).
% 1.68/0.58  fof(f363,plain,(
% 1.68/0.58    ( ! [X1] : (sK3 != X1) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f355,f76])).
% 1.68/0.58  fof(f76,plain,(
% 1.68/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.68/0.58    inference(superposition,[],[f39,f67])).
% 1.68/0.58  fof(f67,plain,(
% 1.68/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.68/0.58    inference(equality_resolution,[],[f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.68/0.58    inference(cnf_transformation,[],[f23])).
% 1.68/0.58  fof(f23,plain,(
% 1.68/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.68/0.58    inference(flattening,[],[f22])).
% 1.68/0.58  fof(f22,plain,(
% 1.68/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.68/0.58    inference(nnf_transformation,[],[f3])).
% 1.68/0.58  fof(f3,axiom,(
% 1.68/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f4])).
% 1.68/0.58  fof(f4,axiom,(
% 1.68/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.68/0.58  fof(f355,plain,(
% 1.68/0.58    ( ! [X1] : (r2_hidden(sK3,k1_xboole_0) | sK3 != X1) )),
% 1.68/0.58    inference(superposition,[],[f70,f332])).
% 1.68/0.58  fof(f332,plain,(
% 1.68/0.58    ( ! [X0] : (k1_xboole_0 = k1_enumset1(X0,X0,sK3) | sK3 != X0) )),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f331])).
% 1.68/0.58  fof(f331,plain,(
% 1.68/0.58    ( ! [X0] : (sK3 != X0 | k1_xboole_0 = k1_enumset1(X0,X0,sK3) | sK3 != X0) )),
% 1.68/0.58    inference(forward_demodulation,[],[f325,f310])).
% 1.68/0.58  fof(f310,plain,(
% 1.68/0.58    sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 1.68/0.58    inference(backward_demodulation,[],[f161,f308])).
% 1.68/0.58  fof(f308,plain,(
% 1.68/0.58    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(trivial_inequality_removal,[],[f307])).
% 1.68/0.58  fof(f307,plain,(
% 1.68/0.58    sK3 != sK3 | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(superposition,[],[f303,f171])).
% 1.68/0.58  fof(f171,plain,(
% 1.68/0.58    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(subsumption_resolution,[],[f164,f120])).
% 1.68/0.58  fof(f120,plain,(
% 1.68/0.58    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(superposition,[],[f74,f111])).
% 1.68/0.58  fof(f111,plain,(
% 1.68/0.58    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.68/0.58    inference(subsumption_resolution,[],[f110,f29])).
% 1.68/0.58  fof(f29,plain,(
% 1.68/0.58    k1_xboole_0 != sK0),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f19,plain,(
% 1.68/0.58    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18,f17])).
% 1.68/0.58  fof(f17,plain,(
% 1.68/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f18,plain,(
% 1.68/0.58    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f13,plain,(
% 1.68/0.58    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.68/0.58    inference(ennf_transformation,[],[f12])).
% 1.68/0.58  fof(f12,negated_conjecture,(
% 1.68/0.58    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.68/0.58    inference(negated_conjecture,[],[f11])).
% 1.68/0.58  fof(f11,conjecture,(
% 1.68/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.68/0.58  fof(f110,plain,(
% 1.68/0.58    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 1.68/0.58    inference(subsumption_resolution,[],[f109,f30])).
% 1.68/0.58  fof(f30,plain,(
% 1.68/0.58    k1_xboole_0 != sK1),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f109,plain,(
% 1.68/0.58    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.68/0.58    inference(subsumption_resolution,[],[f105,f31])).
% 1.68/0.58  fof(f31,plain,(
% 1.68/0.58    k1_xboole_0 != sK2),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f105,plain,(
% 1.68/0.58    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.68/0.58    inference(resolution,[],[f64,f55])).
% 1.68/0.58  fof(f55,plain,(
% 1.68/0.58    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.68/0.58    inference(definition_unfolding,[],[f32,f46])).
% 1.68/0.58  fof(f46,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f64,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.68/0.58    inference(definition_unfolding,[],[f54,f47,f46])).
% 1.68/0.58  fof(f47,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f5])).
% 1.68/0.58  fof(f5,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.68/0.58  fof(f54,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f16,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.68/0.58    inference(ennf_transformation,[],[f9])).
% 1.68/0.58  fof(f9,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.68/0.58  fof(f74,plain,(
% 1.68/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.68/0.58    inference(backward_demodulation,[],[f65,f42])).
% 1.68/0.58  fof(f42,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.68/0.58    inference(cnf_transformation,[],[f10])).
% 1.68/0.58  fof(f10,axiom,(
% 1.68/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.68/0.58  fof(f65,plain,(
% 1.68/0.58    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.68/0.58    inference(equality_resolution,[],[f35])).
% 1.68/0.58  fof(f35,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f14])).
% 1.68/0.58  fof(f14,plain,(
% 1.68/0.58    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.68/0.58    inference(ennf_transformation,[],[f7])).
% 1.68/0.58  fof(f7,axiom,(
% 1.68/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.68/0.58  fof(f164,plain,(
% 1.68/0.58    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(backward_demodulation,[],[f33,f160])).
% 1.68/0.58  fof(f160,plain,(
% 1.68/0.58    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.68/0.58    inference(superposition,[],[f42,f118])).
% 1.68/0.58  fof(f118,plain,(
% 1.68/0.58    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) = k1_mcart_1(sK3)),
% 1.68/0.58    inference(superposition,[],[f41,f111])).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f10])).
% 1.68/0.58  fof(f33,plain,(
% 1.68/0.58    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f303,plain,(
% 1.68/0.58    sK3 != k2_mcart_1(k1_mcart_1(sK3))),
% 1.68/0.58    inference(equality_resolution,[],[f295])).
% 1.68/0.58  fof(f295,plain,(
% 1.68/0.58    ( ! [X1] : (k2_mcart_1(k1_mcart_1(sK3)) != X1 | sK3 != X1) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f285,f76])).
% 1.68/0.58  fof(f285,plain,(
% 1.68/0.58    ( ! [X1] : (r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_xboole_0) | sK3 != X1 | k2_mcart_1(k1_mcart_1(sK3)) != X1) )),
% 1.68/0.58    inference(superposition,[],[f70,f279])).
% 1.68/0.58  fof(f279,plain,(
% 1.68/0.58    ( ! [X0] : (k1_xboole_0 = k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3))) | sK3 != X0 | k2_mcart_1(k1_mcart_1(sK3)) != X0) )),
% 1.68/0.58    inference(superposition,[],[f172,f98])).
% 1.68/0.58  fof(f98,plain,(
% 1.68/0.58    ( ! [X0,X1] : (sK4(k1_enumset1(X0,X0,X1)) = X0 | X0 != X1) )),
% 1.68/0.58    inference(equality_factoring,[],[f87])).
% 1.68/0.58  fof(f87,plain,(
% 1.68/0.58    ( ! [X4,X3] : (sK4(k1_enumset1(X3,X3,X4)) = X4 | sK4(k1_enumset1(X3,X3,X4)) = X3) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f85,f76])).
% 1.68/0.58  fof(f85,plain,(
% 1.68/0.58    ( ! [X4,X3] : (r2_hidden(X3,k1_xboole_0) | sK4(k1_enumset1(X3,X3,X4)) = X4 | sK4(k1_enumset1(X3,X3,X4)) = X3) )),
% 1.68/0.58    inference(superposition,[],[f72,f83])).
% 1.68/0.58  fof(f83,plain,(
% 1.68/0.58    ( ! [X4,X5] : (k1_xboole_0 = k1_enumset1(X4,X4,X5) | sK4(k1_enumset1(X4,X4,X5)) = X5 | sK4(k1_enumset1(X4,X4,X5)) = X4) )),
% 1.68/0.58    inference(resolution,[],[f73,f36])).
% 1.68/0.58  fof(f36,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f21])).
% 1.68/0.58  fof(f21,plain,(
% 1.68/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 1.68/0.58  fof(f20,plain,(
% 1.68/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f15,plain,(
% 1.68/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.68/0.58    inference(ennf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.68/0.58  fof(f73,plain,(
% 1.68/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.68/0.58    inference(equality_resolution,[],[f63])).
% 1.68/0.58  fof(f63,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.68/0.58    inference(definition_unfolding,[],[f48,f40])).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f2])).
% 1.68/0.58  fof(f2,axiom,(
% 1.68/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f26,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(rectify,[],[f25])).
% 1.68/0.58  fof(f25,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(flattening,[],[f24])).
% 1.68/0.58  fof(f24,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(nnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.68/0.58  fof(f72,plain,(
% 1.68/0.58    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 1.68/0.58    inference(equality_resolution,[],[f71])).
% 1.68/0.58  fof(f71,plain,(
% 1.68/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 1.68/0.58    inference(equality_resolution,[],[f62])).
% 1.68/0.58  fof(f62,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 1.68/0.58    inference(definition_unfolding,[],[f49,f40])).
% 1.68/0.58  fof(f49,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f28])).
% 1.68/0.58  fof(f172,plain,(
% 1.68/0.58    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3)))) | k1_xboole_0 = k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3)))) )),
% 1.68/0.58    inference(forward_demodulation,[],[f168,f160])).
% 1.68/0.58  fof(f168,plain,(
% 1.68/0.58    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k2_mcart_1(k1_mcart_1(sK3)))) | k1_xboole_0 = k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3))) )),
% 1.68/0.58    inference(backward_demodulation,[],[f155,f160])).
% 1.68/0.59  fof(f155,plain,(
% 1.68/0.59    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3))) | k1_xboole_0 = k1_enumset1(X0,X0,k6_mcart_1(sK0,sK1,sK2,sK3))) )),
% 1.68/0.59    inference(resolution,[],[f114,f70])).
% 1.68/0.59  fof(f114,plain,(
% 1.68/0.59    ( ! [X1] : (~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),X1) | sK3 != sK4(X1) | k1_xboole_0 = X1) )),
% 1.68/0.59    inference(superposition,[],[f56,f111])).
% 1.68/0.59  fof(f56,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(definition_unfolding,[],[f38,f47])).
% 1.68/0.59  fof(f38,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f21])).
% 1.68/0.59  fof(f161,plain,(
% 1.68/0.59    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.68/0.59    inference(superposition,[],[f41,f118])).
% 1.68/0.59  fof(f325,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k1_enumset1(X0,X0,sK3) | sK3 != X0 | k1_mcart_1(k1_mcart_1(sK3)) != X0) )),
% 1.68/0.59    inference(backward_demodulation,[],[f299,f310])).
% 1.68/0.59  fof(f299,plain,(
% 1.68/0.59    ( ! [X0] : (sK3 != X0 | k1_xboole_0 = k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3))) | k1_mcart_1(k1_mcart_1(sK3)) != X0) )),
% 1.68/0.59    inference(superposition,[],[f181,f98])).
% 1.68/0.59  fof(f181,plain,(
% 1.68/0.59    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3)))) | k1_xboole_0 = k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3)))) )),
% 1.68/0.59    inference(forward_demodulation,[],[f176,f161])).
% 1.68/0.59  fof(f176,plain,(
% 1.68/0.59    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k1_mcart_1(k1_mcart_1(sK3)))) | k1_xboole_0 = k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3))) )),
% 1.68/0.59    inference(backward_demodulation,[],[f153,f161])).
% 1.68/0.59  fof(f153,plain,(
% 1.68/0.59    ( ! [X0] : (sK3 != sK4(k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3))) | k1_xboole_0 = k1_enumset1(X0,X0,k5_mcart_1(sK0,sK1,sK2,sK3))) )),
% 1.68/0.59    inference(resolution,[],[f113,f70])).
% 1.68/0.59  fof(f113,plain,(
% 1.68/0.59    ( ! [X0] : (~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0) | sK3 != sK4(X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(superposition,[],[f57,f111])).
% 1.68/0.59  fof(f57,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(definition_unfolding,[],[f37,f47])).
% 1.68/0.59  fof(f37,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f21])).
% 1.68/0.59  fof(f70,plain,(
% 1.68/0.59    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 1.68/0.59    inference(equality_resolution,[],[f69])).
% 1.68/0.59  fof(f69,plain,(
% 1.68/0.59    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 1.68/0.59    inference(equality_resolution,[],[f61])).
% 1.68/0.59  fof(f61,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 1.68/0.59    inference(definition_unfolding,[],[f50,f40])).
% 1.68/0.59  fof(f50,plain,(
% 1.68/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.68/0.59    inference(cnf_transformation,[],[f28])).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (26603)------------------------------
% 1.68/0.59  % (26603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (26603)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (26603)Memory used [KB]: 6524
% 1.68/0.59  % (26603)Time elapsed: 0.162 s
% 1.68/0.59  % (26603)------------------------------
% 1.68/0.59  % (26603)------------------------------
% 1.81/0.59  % (26580)Success in time 0.227 s
%------------------------------------------------------------------------------
