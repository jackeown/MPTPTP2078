%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:08 EST 2020

% Result     : Theorem 6.09s
% Output     : Refutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :  147 (1877 expanded)
%              Number of leaves         :   23 ( 686 expanded)
%              Depth                    :   37
%              Number of atoms          :  624 (10687 expanded)
%              Number of equality atoms :  429 (8198 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2856,plain,(
    $false ),
    inference(equality_resolution,[],[f2766])).

fof(f2766,plain,(
    ! [X0] : sK3 != X0 ),
    inference(subsumption_resolution,[],[f2765,f2398])).

fof(f2398,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(superposition,[],[f115,f2393])).

fof(f2393,plain,(
    k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),sK3) ),
    inference(trivial_inequality_removal,[],[f2387])).

fof(f2387,plain,
    ( k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),sK3)
    | sK3 != sK3 ),
    inference(resolution,[],[f2363,f115])).

fof(f2363,plain,(
    ! [X23] :
      ( ~ r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23)
      | sK3 != X23 ) ),
    inference(subsumption_resolution,[],[f2350,f2359])).

fof(f2359,plain,(
    ! [X6,X8,X7] :
      ( k1_mcart_1(sK3) != k4_tarski(X7,X8)
      | ~ r2_hidden(X8,k2_tarski(k1_mcart_1(sK3),X6))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6)
      | sK3 != X6 ) ),
    inference(duplicate_literal_removal,[],[f2341])).

fof(f2341,plain,(
    ! [X6,X8,X7] :
      ( k1_mcart_1(sK3) != k4_tarski(X7,X8)
      | ~ r2_hidden(X8,k2_tarski(k1_mcart_1(sK3),X6))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6)
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6)
      | sK3 != X6 ) ),
    inference(superposition,[],[f67,f2302])).

fof(f2302,plain,(
    ! [X4] :
      ( k1_mcart_1(sK3) = sK7(k2_tarski(k1_mcart_1(sK3),X4))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X4)
      | sK3 != X4 ) ),
    inference(resolution,[],[f389,f117])).

fof(f117,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK8(X0,X1,X2) != X1
              & sK8(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X1
            | sK8(X0,X1,X2) = X0
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X1
            & sK8(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X1
          | sK8(X0,X1,X2) = X0
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f389,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK3),k2_tarski(X0,X1))
      | sK3 != X1
      | k2_tarski(X0,X1) = k1_xboole_0
      | sK7(k2_tarski(X0,X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,(
    ! [X0,X1] :
      ( sK3 != X1
      | ~ r2_hidden(k1_mcart_1(sK3),k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = k1_xboole_0
      | sK7(k2_tarski(X0,X1)) = X0
      | k2_tarski(X0,X1) = k1_xboole_0 ) ),
    inference(superposition,[],[f326,f130])).

fof(f130,plain,(
    ! [X4,X5] :
      ( sK7(k2_tarski(X4,X5)) = X5
      | sK7(k2_tarski(X4,X5)) = X4
      | k1_xboole_0 = k2_tarski(X4,X5) ) ),
    inference(resolution,[],[f118,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f326,plain,(
    ! [X1] :
      ( sK3 != sK7(X1)
      | ~ r2_hidden(k1_mcart_1(sK3),X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f316,f318])).

fof(f318,plain,(
    k1_mcart_1(sK3) = k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f68,f314])).

fof(f314,plain,(
    sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f313,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f313,plain,
    ( sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f312,f56])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f312,plain,
    ( sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f305,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f305,plain,
    ( sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f106,f102])).

fof(f102,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f58,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3)),sK16(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f101,f76,f77])).

fof(f76,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK16(X0,X1,X2,X3),X2)
            & m1_subset_1(sK15(X0,X1,X2,X3),X1)
            & m1_subset_1(sK14(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f24,f53,f52,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK14(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK14(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK14(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK15(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK16(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f68,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f316,plain,(
    ! [X1] :
      ( sK3 != sK7(X1)
      | ~ r2_hidden(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f66,f314])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK7(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK7(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2350,plain,(
    ! [X23] :
      ( ~ r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23)
      | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
      | sK3 != X23 ) ),
    inference(trivial_inequality_removal,[],[f2349])).

fof(f2349,plain,(
    ! [X23] :
      ( k1_mcart_1(sK3) != k1_mcart_1(sK3)
      | ~ r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23)
      | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
      | sK3 != X23 ) ),
    inference(duplicate_literal_removal,[],[f2348])).

fof(f2348,plain,(
    ! [X23] :
      ( k1_mcart_1(sK3) != k1_mcart_1(sK3)
      | ~ r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23))
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23)
      | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)
      | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23)
      | sK3 != X23 ) ),
    inference(superposition,[],[f670,f2302])).

fof(f670,plain,(
    ! [X1] :
      ( k1_mcart_1(sK3) != sK7(X1)
      | ~ r2_hidden(sK3,X1)
      | k1_xboole_0 = X1
      | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) ) ),
    inference(superposition,[],[f66,f618])).

fof(f618,plain,
    ( k1_mcart_1(sK3) = k4_tarski(sK3,k2_mcart_1(k1_mcart_1(sK3)))
    | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) ),
    inference(superposition,[],[f448,f571])).

fof(f571,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) ),
    inference(superposition,[],[f448,f348])).

fof(f348,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f338,f124])).

fof(f124,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f110,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f110,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f338,plain,
    ( sK3 = k4_tarski(k1_mcart_1(sK3),sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f328,f304])).

fof(f304,plain,
    ( sK3 = k2_mcart_1(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f303,f55])).

fof(f303,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f302,f56])).

fof(f302,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f301,f57])).

fof(f301,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f299,f102])).

fof(f299,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f105,f291])).

fof(f291,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f290,f55])).

fof(f290,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f289,f56])).

fof(f289,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f288,f57])).

fof(f288,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f286,f102])).

fof(f286,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f104,f256])).

fof(f256,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f255,f55])).

fof(f255,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f254,f56])).

fof(f254,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f253,f57])).

fof(f253,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f251,f102])).

fof(f251,plain,
    ( sK3 = k2_mcart_1(sK3)
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f103,f59])).

fof(f59,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f97,f77])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f96,f77])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f95,f77])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f328,plain,(
    sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f327,f319])).

fof(f319,plain,(
    k2_mcart_1(sK3) = sK16(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f69,f314])).

fof(f327,plain,(
    sK3 = k4_tarski(k1_mcart_1(sK3),sK16(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f314,f318])).

fof(f448,plain,(
    k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3))) ),
    inference(backward_demodulation,[],[f447,f437])).

fof(f437,plain,(
    k2_mcart_1(k1_mcart_1(sK3)) = sK15(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f69,f318])).

fof(f447,plain,(
    k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK15(sK0,sK1,sK2,sK3)) ),
    inference(backward_demodulation,[],[f318,f436])).

fof(f436,plain,(
    k1_mcart_1(k1_mcart_1(sK3)) = sK14(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f68,f318])).

fof(f115,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2765,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k1_xboole_0)
      | sK3 != X0 ) ),
    inference(forward_demodulation,[],[f2760,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2760,plain,(
    ! [X0] :
      ( sK3 != X0
      | ~ r2_hidden(sK3,k2_zfmisc_1(k1_tarski(X0),k1_xboole_0)) ) ),
    inference(superposition,[],[f2684,f235])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( sK12(k1_tarski(X0),X1,X2) = X0
      | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) ) ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( X0 != X0
      | sK12(k1_tarski(X0),X1,X2) = X0
      | ~ r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1)) ) ),
    inference(equality_factoring,[],[f194])).

fof(f194,plain,(
    ! [X14,X12,X15,X13] :
      ( sK12(k1_tarski(X12),X13,X14) = X12
      | X12 = X15
      | ~ r2_hidden(X14,k2_zfmisc_1(k1_tarski(X12),X13)) ) ),
    inference(resolution,[],[f183,f123])).

fof(f123,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
              & r2_hidden(sK11(X0,X1,X2),X1)
              & r2_hidden(sK10(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
                & r2_hidden(sK13(X0,X1,X8),X1)
                & r2_hidden(sK12(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f44,f47,f46,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
        & r2_hidden(sK11(X0,X1,X2),X1)
        & r2_hidden(sK10(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
        & r2_hidden(sK13(X0,X1,X8),X1)
        & r2_hidden(sK12(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2
      | X0 = X2 ) ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k2_tarski(X0,X1)
      | ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2
      | X0 = X2 ) ),
    inference(superposition,[],[f93,f131])).

fof(f131,plain,(
    ! [X6,X8,X7] :
      ( k2_tarski(X6,X8) = k4_xboole_0(k2_tarski(X6,X8),k1_tarski(X7))
      | X7 = X8
      | X6 = X7 ) ),
    inference(resolution,[],[f118,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f2684,plain,(
    ! [X16] : sK3 != sK12(X16,k1_xboole_0,sK3) ),
    inference(superposition,[],[f125,f2459])).

fof(f2459,plain,(
    ! [X0] : sK3 = k4_tarski(sK12(X0,k1_xboole_0,sK3),sK13(X0,k1_xboole_0,sK3)) ),
    inference(resolution,[],[f2398,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | k4_tarski(sK12(X0,k1_xboole_0,X1),sK13(X0,k1_xboole_0,X1)) = X1 ) ),
    inference(superposition,[],[f121,f112])).

fof(f121,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f125,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X1 ),
    inference(backward_demodulation,[],[f111,f68])).

fof(f111,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (12362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (12342)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (12342)Refutation not found, incomplete strategy% (12342)------------------------------
% 0.20/0.52  % (12342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12342)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12342)Memory used [KB]: 1663
% 0.20/0.52  % (12342)Time elapsed: 0.084 s
% 0.20/0.52  % (12342)------------------------------
% 0.20/0.52  % (12342)------------------------------
% 0.20/0.54  % (12351)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (12341)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (12346)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.57  % (12348)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (12345)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.58  % (12343)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.58  % (12361)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.58  % (12365)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.60  % (12364)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.60  % (12359)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.60  % (12363)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.60  % (12368)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.60  % (12356)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.60  % (12353)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.60  % (12357)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.60  % (12350)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.60  % (12356)Refutation not found, incomplete strategy% (12356)------------------------------
% 0.20/0.60  % (12356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (12356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.61  % (12355)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.61  % (12360)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.62  % (12371)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.62  % (12352)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.62  % (12371)Refutation not found, incomplete strategy% (12371)------------------------------
% 0.20/0.62  % (12371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (12371)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (12371)Memory used [KB]: 1663
% 0.20/0.62  % (12371)Time elapsed: 0.002 s
% 0.20/0.62  % (12371)------------------------------
% 0.20/0.62  % (12371)------------------------------
% 0.20/0.62  % (12370)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.62  % (12349)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.62  % (12369)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.62  % (12356)Memory used [KB]: 1791
% 0.20/0.62  % (12356)Time elapsed: 0.170 s
% 0.20/0.62  % (12356)------------------------------
% 0.20/0.62  % (12356)------------------------------
% 0.20/0.62  % (12344)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.62  % (12368)Refutation not found, incomplete strategy% (12368)------------------------------
% 0.20/0.62  % (12368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (12368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (12368)Memory used [KB]: 6268
% 0.20/0.62  % (12368)Time elapsed: 0.200 s
% 0.20/0.62  % (12368)------------------------------
% 0.20/0.62  % (12368)------------------------------
% 0.20/0.63  % (12367)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.63  % (12360)Refutation not found, incomplete strategy% (12360)------------------------------
% 0.20/0.63  % (12360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (12360)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.63  
% 0.20/0.63  % (12360)Memory used [KB]: 1791
% 0.20/0.63  % (12360)Time elapsed: 0.200 s
% 0.20/0.63  % (12360)------------------------------
% 0.20/0.63  % (12360)------------------------------
% 0.20/0.63  % (12352)Refutation not found, incomplete strategy% (12352)------------------------------
% 0.20/0.63  % (12352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (12352)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.63  
% 0.20/0.63  % (12352)Memory used [KB]: 10874
% 0.20/0.63  % (12352)Time elapsed: 0.204 s
% 0.20/0.63  % (12352)------------------------------
% 0.20/0.63  % (12352)------------------------------
% 0.20/0.64  % (12354)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.64  % (12354)Refutation not found, incomplete strategy% (12354)------------------------------
% 0.20/0.64  % (12354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.64  % (12354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.64  
% 0.20/0.64  % (12354)Memory used [KB]: 10618
% 0.20/0.64  % (12354)Time elapsed: 0.211 s
% 0.20/0.64  % (12354)------------------------------
% 0.20/0.64  % (12354)------------------------------
% 0.20/0.65  % (12370)Refutation not found, incomplete strategy% (12370)------------------------------
% 0.20/0.65  % (12370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.65  % (12370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.65  
% 0.20/0.65  % (12370)Memory used [KB]: 10874
% 0.20/0.65  % (12370)Time elapsed: 0.193 s
% 0.20/0.65  % (12370)------------------------------
% 0.20/0.65  % (12370)------------------------------
% 0.20/0.66  % (12358)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.67  % (12366)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.67  % (12366)Refutation not found, incomplete strategy% (12366)------------------------------
% 0.20/0.67  % (12366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.67  % (12366)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.67  
% 0.20/0.67  % (12366)Memory used [KB]: 10746
% 0.20/0.67  % (12366)Time elapsed: 0.238 s
% 0.20/0.67  % (12366)------------------------------
% 0.20/0.67  % (12366)------------------------------
% 0.20/0.68  % (12358)Refutation not found, incomplete strategy% (12358)------------------------------
% 0.20/0.68  % (12358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.68  % (12358)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.68  
% 0.20/0.68  % (12358)Memory used [KB]: 10746
% 0.20/0.68  % (12358)Time elapsed: 0.247 s
% 0.20/0.68  % (12358)------------------------------
% 0.20/0.68  % (12358)------------------------------
% 2.72/0.72  % (12402)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.85/0.74  % (12404)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.85/0.74  % (12404)Refutation not found, incomplete strategy% (12404)------------------------------
% 2.85/0.74  % (12404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.74  % (12404)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.74  
% 2.85/0.74  % (12404)Memory used [KB]: 6268
% 2.85/0.74  % (12404)Time elapsed: 0.070 s
% 2.85/0.74  % (12404)------------------------------
% 2.85/0.74  % (12404)------------------------------
% 2.85/0.75  % (12407)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.85/0.76  % (12408)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.85/0.76  % (12406)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.85/0.76  % (12403)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.85/0.77  % (12405)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.85/0.78  % (12344)Refutation not found, incomplete strategy% (12344)------------------------------
% 2.85/0.78  % (12344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.78  % (12344)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.78  
% 2.85/0.78  % (12344)Memory used [KB]: 6140
% 2.85/0.78  % (12344)Time elapsed: 0.340 s
% 2.85/0.78  % (12344)------------------------------
% 2.85/0.78  % (12344)------------------------------
% 2.85/0.78  % (12409)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.85/0.78  % (12341)Refutation not found, incomplete strategy% (12341)------------------------------
% 2.85/0.78  % (12341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.78  % (12341)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.78  
% 2.85/0.78  % (12341)Memory used [KB]: 1791
% 2.85/0.78  % (12341)Time elapsed: 0.339 s
% 2.85/0.78  % (12341)------------------------------
% 2.85/0.78  % (12341)------------------------------
% 2.85/0.79  % (12357)Refutation not found, incomplete strategy% (12357)------------------------------
% 2.85/0.79  % (12357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.79  % (12357)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.79  
% 2.85/0.79  % (12357)Memory used [KB]: 6268
% 2.85/0.79  % (12357)Time elapsed: 0.326 s
% 2.85/0.79  % (12357)------------------------------
% 2.85/0.79  % (12357)------------------------------
% 2.85/0.82  % (12411)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.85/0.82  % (12410)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.62/0.84  % (12343)Time limit reached!
% 3.62/0.84  % (12343)------------------------------
% 3.62/0.84  % (12343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.84  % (12343)Termination reason: Time limit
% 3.62/0.84  
% 3.62/0.84  % (12343)Memory used [KB]: 6524
% 3.62/0.84  % (12343)Time elapsed: 0.411 s
% 3.62/0.84  % (12343)------------------------------
% 3.62/0.84  % (12343)------------------------------
% 3.62/0.84  % (12411)Refutation not found, incomplete strategy% (12411)------------------------------
% 3.62/0.84  % (12411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.84  % (12411)Termination reason: Refutation not found, incomplete strategy
% 3.62/0.84  
% 3.62/0.84  % (12411)Memory used [KB]: 10874
% 3.62/0.84  % (12411)Time elapsed: 0.123 s
% 3.62/0.84  % (12411)------------------------------
% 3.62/0.84  % (12411)------------------------------
% 3.62/0.86  % (12412)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.11/0.91  % (12424)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.11/0.92  % (12420)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.11/0.92  % (12427)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.11/0.93  % (12427)Refutation not found, incomplete strategy% (12427)------------------------------
% 4.11/0.93  % (12427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.93  % (12427)Termination reason: Refutation not found, incomplete strategy
% 4.11/0.93  
% 4.11/0.93  % (12427)Memory used [KB]: 10746
% 4.11/0.93  % (12427)Time elapsed: 0.113 s
% 4.11/0.93  % (12427)------------------------------
% 4.11/0.93  % (12427)------------------------------
% 4.11/0.95  % (12348)Time limit reached!
% 4.11/0.95  % (12348)------------------------------
% 4.11/0.95  % (12348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.95  % (12348)Termination reason: Time limit
% 4.11/0.95  
% 4.11/0.95  % (12348)Memory used [KB]: 14200
% 4.11/0.95  % (12348)Time elapsed: 0.523 s
% 4.11/0.95  % (12348)------------------------------
% 4.11/0.95  % (12348)------------------------------
% 4.11/0.97  % (12453)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 4.59/0.97  % (12451)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 4.59/1.06  % (12490)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 4.59/1.07  % (12349)Time limit reached!
% 4.59/1.07  % (12349)------------------------------
% 4.59/1.07  % (12349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/1.07  % (12349)Termination reason: Time limit
% 4.59/1.07  
% 5.20/1.07  % (12349)Memory used [KB]: 4093
% 5.20/1.07  % (12349)Time elapsed: 0.607 s
% 5.20/1.07  % (12349)------------------------------
% 5.20/1.07  % (12349)------------------------------
% 5.20/1.09  % (12509)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 5.52/1.13  % (12453)Refutation not found, incomplete strategy% (12453)------------------------------
% 5.52/1.13  % (12453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.13  % (12453)Termination reason: Refutation not found, incomplete strategy
% 5.52/1.13  
% 5.52/1.13  % (12453)Memory used [KB]: 6268
% 5.52/1.13  % (12453)Time elapsed: 0.259 s
% 5.52/1.13  % (12453)------------------------------
% 5.52/1.13  % (12453)------------------------------
% 5.52/1.14  % (12451)Refutation not found, incomplete strategy% (12451)------------------------------
% 5.52/1.14  % (12451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.14  % (12451)Termination reason: Refutation not found, incomplete strategy
% 5.52/1.14  
% 5.52/1.14  % (12451)Memory used [KB]: 6396
% 5.52/1.14  % (12451)Time elapsed: 0.258 s
% 5.52/1.14  % (12451)------------------------------
% 5.52/1.14  % (12451)------------------------------
% 6.09/1.20  % (12568)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 6.09/1.24  % (12364)Refutation found. Thanks to Tanya!
% 6.09/1.24  % SZS status Theorem for theBenchmark
% 6.09/1.25  % SZS output start Proof for theBenchmark
% 6.09/1.25  fof(f2856,plain,(
% 6.09/1.25    $false),
% 6.09/1.25    inference(equality_resolution,[],[f2766])).
% 6.09/1.25  fof(f2766,plain,(
% 6.09/1.25    ( ! [X0] : (sK3 != X0) )),
% 6.09/1.25    inference(subsumption_resolution,[],[f2765,f2398])).
% 6.09/1.25  fof(f2398,plain,(
% 6.09/1.25    r2_hidden(sK3,k1_xboole_0)),
% 6.09/1.25    inference(superposition,[],[f115,f2393])).
% 6.09/1.25  fof(f2393,plain,(
% 6.09/1.25    k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),sK3)),
% 6.09/1.25    inference(trivial_inequality_removal,[],[f2387])).
% 6.09/1.25  fof(f2387,plain,(
% 6.09/1.25    k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),sK3) | sK3 != sK3),
% 6.09/1.25    inference(resolution,[],[f2363,f115])).
% 6.09/1.25  fof(f2363,plain,(
% 6.09/1.25    ( ! [X23] : (~r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23) | sK3 != X23) )),
% 6.09/1.25    inference(subsumption_resolution,[],[f2350,f2359])).
% 6.09/1.25  fof(f2359,plain,(
% 6.09/1.25    ( ! [X6,X8,X7] : (k1_mcart_1(sK3) != k4_tarski(X7,X8) | ~r2_hidden(X8,k2_tarski(k1_mcart_1(sK3),X6)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6) | sK3 != X6) )),
% 6.09/1.25    inference(duplicate_literal_removal,[],[f2341])).
% 6.09/1.25  fof(f2341,plain,(
% 6.09/1.25    ( ! [X6,X8,X7] : (k1_mcart_1(sK3) != k4_tarski(X7,X8) | ~r2_hidden(X8,k2_tarski(k1_mcart_1(sK3),X6)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X6) | sK3 != X6) )),
% 6.09/1.25    inference(superposition,[],[f67,f2302])).
% 6.09/1.25  fof(f2302,plain,(
% 6.09/1.25    ( ! [X4] : (k1_mcart_1(sK3) = sK7(k2_tarski(k1_mcart_1(sK3),X4)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X4) | sK3 != X4) )),
% 6.09/1.25    inference(resolution,[],[f389,f117])).
% 6.09/1.25  fof(f117,plain,(
% 6.09/1.25    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 6.09/1.25    inference(equality_resolution,[],[f116])).
% 6.09/1.25  fof(f116,plain,(
% 6.09/1.25    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 6.09/1.25    inference(equality_resolution,[],[f79])).
% 6.09/1.25  fof(f79,plain,(
% 6.09/1.25    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.09/1.25    inference(cnf_transformation,[],[f42])).
% 6.09/1.25  fof(f42,plain,(
% 6.09/1.25    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.09/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).
% 6.09/1.25  fof(f41,plain,(
% 6.09/1.25    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f40,plain,(
% 6.09/1.25    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 6.09/1.25    inference(rectify,[],[f39])).
% 6.09/1.25  fof(f39,plain,(
% 6.09/1.25    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.09/1.25    inference(flattening,[],[f38])).
% 6.09/1.25  fof(f38,plain,(
% 6.09/1.25    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 6.09/1.25    inference(nnf_transformation,[],[f1])).
% 6.09/1.25  fof(f1,axiom,(
% 6.09/1.25    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 6.09/1.25  fof(f389,plain,(
% 6.09/1.25    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK3),k2_tarski(X0,X1)) | sK3 != X1 | k2_tarski(X0,X1) = k1_xboole_0 | sK7(k2_tarski(X0,X1)) = X0) )),
% 6.09/1.25    inference(duplicate_literal_removal,[],[f388])).
% 6.09/1.25  fof(f388,plain,(
% 6.09/1.25    ( ! [X0,X1] : (sK3 != X1 | ~r2_hidden(k1_mcart_1(sK3),k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK7(k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k1_xboole_0) )),
% 6.09/1.25    inference(superposition,[],[f326,f130])).
% 6.09/1.25  fof(f130,plain,(
% 6.09/1.25    ( ! [X4,X5] : (sK7(k2_tarski(X4,X5)) = X5 | sK7(k2_tarski(X4,X5)) = X4 | k1_xboole_0 = k2_tarski(X4,X5)) )),
% 6.09/1.25    inference(resolution,[],[f118,f65])).
% 6.09/1.25  fof(f65,plain,(
% 6.09/1.25    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f34])).
% 6.09/1.25  fof(f34,plain,(
% 6.09/1.25    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 6.09/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f33])).
% 6.09/1.25  fof(f33,plain,(
% 6.09/1.25    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f20,plain,(
% 6.09/1.25    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.09/1.25    inference(ennf_transformation,[],[f14])).
% 6.09/1.25  fof(f14,axiom,(
% 6.09/1.25    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 6.09/1.25  fof(f118,plain,(
% 6.09/1.25    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 6.09/1.25    inference(equality_resolution,[],[f78])).
% 6.09/1.25  fof(f78,plain,(
% 6.09/1.25    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 6.09/1.25    inference(cnf_transformation,[],[f42])).
% 6.09/1.25  fof(f326,plain,(
% 6.09/1.25    ( ! [X1] : (sK3 != sK7(X1) | ~r2_hidden(k1_mcart_1(sK3),X1) | k1_xboole_0 = X1) )),
% 6.09/1.25    inference(backward_demodulation,[],[f316,f318])).
% 6.09/1.25  fof(f318,plain,(
% 6.09/1.25    k1_mcart_1(sK3) = k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3))),
% 6.09/1.25    inference(superposition,[],[f68,f314])).
% 6.09/1.25  fof(f314,plain,(
% 6.09/1.25    sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f313,f55])).
% 6.09/1.25  fof(f55,plain,(
% 6.09/1.25    k1_xboole_0 != sK0),
% 6.09/1.25    inference(cnf_transformation,[],[f27])).
% 6.09/1.25  fof(f27,plain,(
% 6.09/1.25    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 6.09/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f26,f25])).
% 6.09/1.25  fof(f25,plain,(
% 6.09/1.25    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f26,plain,(
% 6.09/1.25    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f17,plain,(
% 6.09/1.25    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 6.09/1.25    inference(ennf_transformation,[],[f16])).
% 6.09/1.25  fof(f16,negated_conjecture,(
% 6.09/1.25    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 6.09/1.25    inference(negated_conjecture,[],[f15])).
% 6.09/1.25  fof(f15,conjecture,(
% 6.09/1.25    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 6.09/1.25  fof(f313,plain,(
% 6.09/1.25    sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 6.09/1.25    inference(subsumption_resolution,[],[f312,f56])).
% 6.09/1.25  fof(f56,plain,(
% 6.09/1.25    k1_xboole_0 != sK1),
% 6.09/1.25    inference(cnf_transformation,[],[f27])).
% 6.09/1.25  fof(f312,plain,(
% 6.09/1.25    sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 6.09/1.25    inference(subsumption_resolution,[],[f305,f57])).
% 6.09/1.25  fof(f57,plain,(
% 6.09/1.25    k1_xboole_0 != sK2),
% 6.09/1.25    inference(cnf_transformation,[],[f27])).
% 6.09/1.25  fof(f305,plain,(
% 6.09/1.25    sK3 = k4_tarski(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),sK16(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 6.09/1.25    inference(resolution,[],[f106,f102])).
% 6.09/1.25  fof(f102,plain,(
% 6.09/1.25    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 6.09/1.25    inference(definition_unfolding,[],[f58,f77])).
% 6.09/1.25  fof(f77,plain,(
% 6.09/1.25    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 6.09/1.25    inference(cnf_transformation,[],[f8])).
% 6.09/1.25  fof(f8,axiom,(
% 6.09/1.25    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 6.09/1.25  fof(f58,plain,(
% 6.09/1.25    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 6.09/1.25    inference(cnf_transformation,[],[f27])).
% 6.09/1.25  fof(f106,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3)),sK16(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(definition_unfolding,[],[f101,f76,f77])).
% 6.09/1.25  fof(f76,plain,(
% 6.09/1.25    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 6.09/1.25    inference(cnf_transformation,[],[f7])).
% 6.09/1.25  fof(f7,axiom,(
% 6.09/1.25    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 6.09/1.25  fof(f101,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f54])).
% 6.09/1.25  fof(f54,plain,(
% 6.09/1.25    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3 & m1_subset_1(sK16(X0,X1,X2,X3),X2)) & m1_subset_1(sK15(X0,X1,X2,X3),X1)) & m1_subset_1(sK14(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 6.09/1.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f24,f53,f52,f51])).
% 6.09/1.25  fof(f51,plain,(
% 6.09/1.25    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK14(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK14(X0,X1,X2,X3),X0)))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f52,plain,(
% 6.09/1.25    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK14(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK15(X0,X1,X2,X3),X1)))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f53,plain,(
% 6.09/1.25    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X3 & m1_subset_1(sK16(X0,X1,X2,X3),X2)))),
% 6.09/1.25    introduced(choice_axiom,[])).
% 6.09/1.25  fof(f24,plain,(
% 6.09/1.25    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 6.09/1.25    inference(ennf_transformation,[],[f9])).
% 6.09/1.25  fof(f9,axiom,(
% 6.09/1.25    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 6.09/1.25  fof(f68,plain,(
% 6.09/1.25    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f13])).
% 6.09/1.25  fof(f13,axiom,(
% 6.09/1.25    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 6.09/1.25  fof(f316,plain,(
% 6.09/1.25    ( ! [X1] : (sK3 != sK7(X1) | ~r2_hidden(k4_tarski(sK14(sK0,sK1,sK2,sK3),sK15(sK0,sK1,sK2,sK3)),X1) | k1_xboole_0 = X1) )),
% 6.09/1.25    inference(superposition,[],[f66,f314])).
% 6.09/1.25  fof(f66,plain,(
% 6.09/1.25    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK7(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f34])).
% 6.09/1.25  fof(f67,plain,(
% 6.09/1.25    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK7(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f34])).
% 6.09/1.25  fof(f2350,plain,(
% 6.09/1.25    ( ! [X23] : (~r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23) | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) | sK3 != X23) )),
% 6.09/1.25    inference(trivial_inequality_removal,[],[f2349])).
% 6.09/1.25  fof(f2349,plain,(
% 6.09/1.25    ( ! [X23] : (k1_mcart_1(sK3) != k1_mcart_1(sK3) | ~r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23) | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) | sK3 != X23) )),
% 6.09/1.25    inference(duplicate_literal_removal,[],[f2348])).
% 6.09/1.25  fof(f2348,plain,(
% 6.09/1.25    ( ! [X23] : (k1_mcart_1(sK3) != k1_mcart_1(sK3) | ~r2_hidden(sK3,k2_tarski(k1_mcart_1(sK3),X23)) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23) | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3) | k1_xboole_0 = k2_tarski(k1_mcart_1(sK3),X23) | sK3 != X23) )),
% 6.09/1.25    inference(superposition,[],[f670,f2302])).
% 6.09/1.25  fof(f670,plain,(
% 6.09/1.25    ( ! [X1] : (k1_mcart_1(sK3) != sK7(X1) | ~r2_hidden(sK3,X1) | k1_xboole_0 = X1 | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)) )),
% 6.09/1.25    inference(superposition,[],[f66,f618])).
% 6.09/1.25  fof(f618,plain,(
% 6.09/1.25    k1_mcart_1(sK3) = k4_tarski(sK3,k2_mcart_1(k1_mcart_1(sK3))) | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)),
% 6.09/1.25    inference(superposition,[],[f448,f571])).
% 6.09/1.25  fof(f571,plain,(
% 6.09/1.25    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK3)),
% 6.09/1.25    inference(superposition,[],[f448,f348])).
% 6.09/1.25  fof(f348,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f338,f124])).
% 6.09/1.25  fof(f124,plain,(
% 6.09/1.25    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 6.09/1.25    inference(backward_demodulation,[],[f110,f69])).
% 6.09/1.25  fof(f69,plain,(
% 6.09/1.25    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 6.09/1.25    inference(cnf_transformation,[],[f13])).
% 6.09/1.25  fof(f110,plain,(
% 6.09/1.25    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 6.09/1.25    inference(equality_resolution,[],[f61])).
% 6.09/1.25  fof(f61,plain,(
% 6.09/1.25    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f18])).
% 6.09/1.25  fof(f18,plain,(
% 6.09/1.25    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 6.09/1.25    inference(ennf_transformation,[],[f10])).
% 6.09/1.25  fof(f10,axiom,(
% 6.09/1.25    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 6.09/1.25  fof(f338,plain,(
% 6.09/1.25    sK3 = k4_tarski(k1_mcart_1(sK3),sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(superposition,[],[f328,f304])).
% 6.09/1.25  fof(f304,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f303,f55])).
% 6.09/1.25  fof(f303,plain,(
% 6.09/1.25    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f302,f56])).
% 6.09/1.25  fof(f302,plain,(
% 6.09/1.25    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f301,f57])).
% 6.09/1.25  fof(f301,plain,(
% 6.09/1.25    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f299,f102])).
% 6.09/1.25  fof(f299,plain,(
% 6.09/1.25    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(superposition,[],[f105,f291])).
% 6.09/1.25  fof(f291,plain,(
% 6.09/1.25    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 6.09/1.25    inference(subsumption_resolution,[],[f290,f55])).
% 6.09/1.25  fof(f290,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f289,f56])).
% 6.09/1.25  fof(f289,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f288,f57])).
% 6.09/1.25  fof(f288,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f286,f102])).
% 6.09/1.25  fof(f286,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(superposition,[],[f104,f256])).
% 6.09/1.25  fof(f256,plain,(
% 6.09/1.25    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f255,f55])).
% 6.09/1.25  fof(f255,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f254,f56])).
% 6.09/1.25  fof(f254,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f253,f57])).
% 6.09/1.25  fof(f253,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(subsumption_resolution,[],[f251,f102])).
% 6.09/1.25  fof(f251,plain,(
% 6.09/1.25    sK3 = k2_mcart_1(sK3) | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(superposition,[],[f103,f59])).
% 6.09/1.25  fof(f59,plain,(
% 6.09/1.25    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(cnf_transformation,[],[f27])).
% 6.09/1.25  fof(f103,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(definition_unfolding,[],[f97,f77])).
% 6.09/1.25  fof(f97,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f23])).
% 6.09/1.25  fof(f23,plain,(
% 6.09/1.25    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 6.09/1.25    inference(ennf_transformation,[],[f12])).
% 6.09/1.25  fof(f12,axiom,(
% 6.09/1.25    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 6.09/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 6.09/1.25  fof(f104,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(definition_unfolding,[],[f96,f77])).
% 6.09/1.25  fof(f96,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f23])).
% 6.09/1.25  fof(f105,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(definition_unfolding,[],[f95,f77])).
% 6.09/1.25  fof(f95,plain,(
% 6.09/1.25    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 6.09/1.25    inference(cnf_transformation,[],[f23])).
% 6.09/1.25  fof(f328,plain,(
% 6.09/1.25    sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3))),
% 6.09/1.25    inference(backward_demodulation,[],[f327,f319])).
% 6.09/1.25  fof(f319,plain,(
% 6.09/1.25    k2_mcart_1(sK3) = sK16(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(superposition,[],[f69,f314])).
% 6.09/1.25  fof(f327,plain,(
% 6.09/1.25    sK3 = k4_tarski(k1_mcart_1(sK3),sK16(sK0,sK1,sK2,sK3))),
% 6.09/1.25    inference(backward_demodulation,[],[f314,f318])).
% 6.09/1.25  fof(f448,plain,(
% 6.09/1.25    k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)))),
% 6.09/1.25    inference(backward_demodulation,[],[f447,f437])).
% 6.09/1.25  fof(f437,plain,(
% 6.09/1.25    k2_mcart_1(k1_mcart_1(sK3)) = sK15(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(superposition,[],[f69,f318])).
% 6.09/1.25  fof(f447,plain,(
% 6.09/1.25    k1_mcart_1(sK3) = k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),sK15(sK0,sK1,sK2,sK3))),
% 6.09/1.25    inference(backward_demodulation,[],[f318,f436])).
% 6.09/1.25  fof(f436,plain,(
% 6.09/1.25    k1_mcart_1(k1_mcart_1(sK3)) = sK14(sK0,sK1,sK2,sK3)),
% 6.09/1.25    inference(superposition,[],[f68,f318])).
% 6.09/1.25  fof(f115,plain,(
% 6.09/1.25    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 6.09/1.25    inference(equality_resolution,[],[f114])).
% 6.09/1.25  fof(f114,plain,(
% 6.09/1.25    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 6.09/1.25    inference(equality_resolution,[],[f80])).
% 6.09/1.25  fof(f80,plain,(
% 6.09/1.25    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 6.09/1.25    inference(cnf_transformation,[],[f42])).
% 6.09/1.25  fof(f2765,plain,(
% 6.09/1.25    ( ! [X0] : (~r2_hidden(sK3,k1_xboole_0) | sK3 != X0) )),
% 6.09/1.25    inference(forward_demodulation,[],[f2760,f112])).
% 6.09/1.25  fof(f112,plain,(
% 6.09/1.25    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.09/1.25    inference(equality_resolution,[],[f73])).
% 6.09/1.26  fof(f73,plain,(
% 6.09/1.26    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.09/1.26    inference(cnf_transformation,[],[f36])).
% 6.09/1.26  fof(f36,plain,(
% 6.09/1.26    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.09/1.26    inference(flattening,[],[f35])).
% 6.09/1.26  fof(f35,plain,(
% 6.09/1.26    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.09/1.26    inference(nnf_transformation,[],[f3])).
% 6.09/1.26  fof(f3,axiom,(
% 6.09/1.26    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.09/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.09/1.26  fof(f2760,plain,(
% 6.09/1.26    ( ! [X0] : (sK3 != X0 | ~r2_hidden(sK3,k2_zfmisc_1(k1_tarski(X0),k1_xboole_0))) )),
% 6.09/1.26    inference(superposition,[],[f2684,f235])).
% 6.09/1.26  fof(f235,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (sK12(k1_tarski(X0),X1,X2) = X0 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))) )),
% 6.09/1.26    inference(trivial_inequality_removal,[],[f234])).
% 6.09/1.26  fof(f234,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (X0 != X0 | sK12(k1_tarski(X0),X1,X2) = X0 | ~r2_hidden(X2,k2_zfmisc_1(k1_tarski(X0),X1))) )),
% 6.09/1.26    inference(equality_factoring,[],[f194])).
% 6.09/1.26  fof(f194,plain,(
% 6.09/1.26    ( ! [X14,X12,X15,X13] : (sK12(k1_tarski(X12),X13,X14) = X12 | X12 = X15 | ~r2_hidden(X14,k2_zfmisc_1(k1_tarski(X12),X13))) )),
% 6.09/1.26    inference(resolution,[],[f183,f123])).
% 6.09/1.26  fof(f123,plain,(
% 6.09/1.26    ( ! [X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 6.09/1.26    inference(equality_resolution,[],[f84])).
% 6.09/1.26  fof(f84,plain,(
% 6.09/1.26    ( ! [X2,X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 6.09/1.26    inference(cnf_transformation,[],[f48])).
% 6.09/1.26  fof(f48,plain,(
% 6.09/1.26    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X1) & r2_hidden(sK12(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 6.09/1.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f44,f47,f46,f45])).
% 6.09/1.26  fof(f45,plain,(
% 6.09/1.26    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 6.09/1.26    introduced(choice_axiom,[])).
% 6.09/1.26  fof(f46,plain,(
% 6.09/1.26    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X0)))),
% 6.09/1.26    introduced(choice_axiom,[])).
% 6.09/1.26  fof(f47,plain,(
% 6.09/1.26    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X1) & r2_hidden(sK12(X0,X1,X8),X0)))),
% 6.09/1.26    introduced(choice_axiom,[])).
% 6.09/1.26  fof(f44,plain,(
% 6.09/1.26    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 6.09/1.26    inference(rectify,[],[f43])).
% 6.09/1.26  fof(f43,plain,(
% 6.09/1.26    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 6.09/1.26    inference(nnf_transformation,[],[f2])).
% 6.09/1.26  fof(f2,axiom,(
% 6.09/1.26    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 6.09/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 6.09/1.26  fof(f183,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tarski(X2)) | X1 = X2 | X0 = X2) )),
% 6.09/1.26    inference(trivial_inequality_removal,[],[f178])).
% 6.09/1.26  fof(f178,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k2_tarski(X0,X1) | ~r2_hidden(X1,k1_tarski(X2)) | X1 = X2 | X0 = X2) )),
% 6.09/1.26    inference(superposition,[],[f93,f131])).
% 6.09/1.26  fof(f131,plain,(
% 6.09/1.26    ( ! [X6,X8,X7] : (k2_tarski(X6,X8) = k4_xboole_0(k2_tarski(X6,X8),k1_tarski(X7)) | X7 = X8 | X6 = X7) )),
% 6.09/1.26    inference(resolution,[],[f118,f75])).
% 6.09/1.26  fof(f75,plain,(
% 6.09/1.26    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 6.09/1.26    inference(cnf_transformation,[],[f37])).
% 6.09/1.26  fof(f37,plain,(
% 6.09/1.26    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 6.09/1.26    inference(nnf_transformation,[],[f4])).
% 6.09/1.26  fof(f4,axiom,(
% 6.09/1.26    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 6.09/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 6.09/1.26  fof(f93,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 6.09/1.26    inference(cnf_transformation,[],[f50])).
% 6.09/1.26  fof(f50,plain,(
% 6.09/1.26    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 6.09/1.26    inference(flattening,[],[f49])).
% 6.09/1.26  fof(f49,plain,(
% 6.09/1.26    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 6.09/1.26    inference(nnf_transformation,[],[f5])).
% 6.09/1.26  fof(f5,axiom,(
% 6.09/1.26    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 6.09/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 6.09/1.26  fof(f2684,plain,(
% 6.09/1.26    ( ! [X16] : (sK3 != sK12(X16,k1_xboole_0,sK3)) )),
% 6.09/1.26    inference(superposition,[],[f125,f2459])).
% 6.09/1.26  fof(f2459,plain,(
% 6.09/1.26    ( ! [X0] : (sK3 = k4_tarski(sK12(X0,k1_xboole_0,sK3),sK13(X0,k1_xboole_0,sK3))) )),
% 6.09/1.26    inference(resolution,[],[f2398,f148])).
% 6.09/1.26  fof(f148,plain,(
% 6.09/1.26    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | k4_tarski(sK12(X0,k1_xboole_0,X1),sK13(X0,k1_xboole_0,X1)) = X1) )),
% 6.09/1.26    inference(superposition,[],[f121,f112])).
% 6.09/1.26  fof(f121,plain,(
% 6.09/1.26    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8) )),
% 6.09/1.26    inference(equality_resolution,[],[f86])).
% 6.09/1.26  fof(f86,plain,(
% 6.09/1.26    ( ! [X2,X0,X8,X1] : (k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 6.09/1.26    inference(cnf_transformation,[],[f48])).
% 6.09/1.26  fof(f125,plain,(
% 6.09/1.26    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1) )),
% 6.09/1.26    inference(backward_demodulation,[],[f111,f68])).
% 6.09/1.26  fof(f111,plain,(
% 6.09/1.26    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 6.09/1.26    inference(equality_resolution,[],[f60])).
% 6.09/1.26  fof(f60,plain,(
% 6.09/1.26    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 6.09/1.26    inference(cnf_transformation,[],[f18])).
% 6.09/1.26  % SZS output end Proof for theBenchmark
% 6.09/1.26  % (12364)------------------------------
% 6.09/1.26  % (12364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.09/1.26  % (12364)Termination reason: Refutation
% 6.09/1.26  
% 6.09/1.26  % (12364)Memory used [KB]: 11513
% 6.09/1.26  % (12364)Time elapsed: 0.806 s
% 6.09/1.26  % (12364)------------------------------
% 6.09/1.26  % (12364)------------------------------
% 6.09/1.27  % (12340)Success in time 0.895 s
%------------------------------------------------------------------------------
