%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 921 expanded)
%              Number of leaves         :   16 ( 303 expanded)
%              Depth                    :   20
%              Number of atoms          :  406 (5039 expanded)
%              Number of equality atoms :  248 (3539 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f662,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f304,f304,f84,f632])).

fof(f632,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(sK3,k1_enumset1(X22,X22,X23))
      | sK3 != X22
      | X22 != X23 ) ),
    inference(backward_demodulation,[],[f586,f623])).

fof(f623,plain,(
    sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f622])).

fof(f622,plain,
    ( sK3 != sK3
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f595,f462])).

fof(f462,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f412,f421])).

fof(f421,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f415,f300])).

fof(f300,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f88,f291])).

fof(f291,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f290,f34])).

fof(f34,plain,(
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

fof(f290,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f289,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f289,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f288,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f288,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f77,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f37,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f48,f47])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f64,plain,(
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

fof(f88,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f78,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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

fof(f415,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(backward_demodulation,[],[f38,f411])).

fof(f411,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f46,f298])).

fof(f298,plain,(
    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) = k1_mcart_1(sK3) ),
    inference(superposition,[],[f45,f291])).

fof(f45,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f412,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f45,f298])).

fof(f595,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(equality_resolution,[],[f587])).

fof(f587,plain,(
    ! [X0] :
      ( k2_mcart_1(k1_mcart_1(sK3)) != X0
      | sK3 != X0 ) ),
    inference(resolution,[],[f585,f84])).

fof(f585,plain,(
    ! [X21,X20] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X20,X20,X21))
      | sK3 != X20
      | X20 != X21 ) ),
    inference(subsumption_resolution,[],[f579,f119])).

fof(f119,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) != k1_xboole_0 ),
    inference(subsumption_resolution,[],[f118,f84])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_xboole_0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X1)) ) ),
    inference(superposition,[],[f75,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f91,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
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

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f82,f41])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f62,f44,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f579,plain,(
    ! [X21,X20] :
      ( sK3 != X20
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X20,X20,X21))
      | k1_xboole_0 = k1_enumset1(X20,X20,X21)
      | X20 != X21 ) ),
    inference(superposition,[],[f416,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( sK4(k1_enumset1(X0,X0,X1)) = X0
      | X0 != X1 ) ),
    inference(subsumption_resolution,[],[f313,f119])).

fof(f313,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | sK4(k1_enumset1(X0,X0,X1)) = X0
      | k1_enumset1(X0,X0,X1) = k1_xboole_0 ) ),
    inference(equality_factoring,[],[f101])).

fof(f101,plain,(
    ! [X4,X5] :
      ( sK4(k1_enumset1(X4,X4,X5)) = X5
      | sK4(k1_enumset1(X4,X4,X5)) = X4
      | k1_xboole_0 = k1_enumset1(X4,X4,X5) ) ),
    inference(resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f44])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f416,plain,(
    ! [X1] :
      ( sK3 != sK4(X1)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f294,f411])).

fof(f294,plain,(
    ! [X1] :
      ( sK3 != sK4(X1)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f66,f291])).

fof(f66,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f586,plain,(
    ! [X23,X22] :
      ( sK3 != X22
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X22,X22,X23))
      | X22 != X23 ) ),
    inference(subsumption_resolution,[],[f580,f119])).

fof(f580,plain,(
    ! [X23,X22] :
      ( sK3 != X22
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X22,X22,X23))
      | k1_xboole_0 = k1_enumset1(X22,X22,X23)
      | X22 != X23 ) ),
    inference(superposition,[],[f422,f319])).

fof(f422,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f293,f412])).

fof(f293,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f67,f291])).

fof(f67,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f44])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f304,plain,(
    sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f303,f298])).

fof(f303,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f291,f297])).

fof(f297,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(superposition,[],[f46,f291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (13582)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.49  % (13603)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.50  % (13603)Refutation not found, incomplete strategy% (13603)------------------------------
% 0.21/0.50  % (13603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13603)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13603)Memory used [KB]: 10874
% 0.21/0.51  % (13603)Time elapsed: 0.077 s
% 0.21/0.51  % (13603)------------------------------
% 0.21/0.51  % (13603)------------------------------
% 1.30/0.53  % (13577)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (13592)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.54  % (13600)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.54  % (13585)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.54  % (13578)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.54  % (13592)Refutation not found, incomplete strategy% (13592)------------------------------
% 1.43/0.54  % (13592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (13599)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.56  % (13579)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.56  % (13594)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.56  % (13585)Refutation not found, incomplete strategy% (13585)------------------------------
% 1.43/0.56  % (13585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (13585)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (13585)Memory used [KB]: 10874
% 1.43/0.56  % (13585)Time elapsed: 0.147 s
% 1.43/0.56  % (13585)------------------------------
% 1.43/0.56  % (13585)------------------------------
% 1.43/0.56  % (13575)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.56  % (13588)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (13589)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.56  % (13592)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (13592)Memory used [KB]: 1791
% 1.43/0.56  % (13592)Time elapsed: 0.126 s
% 1.43/0.56  % (13592)------------------------------
% 1.43/0.56  % (13592)------------------------------
% 1.43/0.56  % (13591)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.56  % (13589)Refutation not found, incomplete strategy% (13589)------------------------------
% 1.43/0.56  % (13589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (13589)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (13589)Memory used [KB]: 1791
% 1.43/0.56  % (13589)Time elapsed: 0.091 s
% 1.43/0.56  % (13589)------------------------------
% 1.43/0.56  % (13589)------------------------------
% 1.43/0.56  % (13591)Refutation not found, incomplete strategy% (13591)------------------------------
% 1.43/0.56  % (13591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (13591)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (13591)Memory used [KB]: 10618
% 1.43/0.56  % (13591)Time elapsed: 0.146 s
% 1.43/0.56  % (13591)------------------------------
% 1.43/0.56  % (13591)------------------------------
% 1.43/0.56  % (13584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.56  % (13581)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (13598)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.57  % (13602)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.57  % (13576)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.43/0.57  % (13587)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.57  % (13599)Refutation not found, incomplete strategy% (13599)------------------------------
% 1.43/0.57  % (13599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (13576)Refutation not found, incomplete strategy% (13576)------------------------------
% 1.43/0.57  % (13576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (13576)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (13576)Memory used [KB]: 1663
% 1.43/0.57  % (13576)Time elapsed: 0.147 s
% 1.43/0.57  % (13576)------------------------------
% 1.43/0.57  % (13576)------------------------------
% 1.43/0.57  % (13599)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (13599)Memory used [KB]: 10746
% 1.43/0.57  % (13599)Time elapsed: 0.154 s
% 1.43/0.57  % (13599)------------------------------
% 1.43/0.57  % (13599)------------------------------
% 1.43/0.57  % (13602)Refutation not found, incomplete strategy% (13602)------------------------------
% 1.43/0.57  % (13602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (13602)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (13602)Memory used [KB]: 6268
% 1.43/0.57  % (13602)Time elapsed: 0.153 s
% 1.43/0.57  % (13602)------------------------------
% 1.43/0.57  % (13602)------------------------------
% 1.43/0.57  % (13587)Refutation not found, incomplete strategy% (13587)------------------------------
% 1.43/0.57  % (13587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (13587)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (13587)Memory used [KB]: 10618
% 1.43/0.57  % (13587)Time elapsed: 0.156 s
% 1.43/0.57  % (13587)------------------------------
% 1.43/0.57  % (13587)------------------------------
% 1.43/0.57  % (13596)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.57  % (13590)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.57  % (13595)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.57  % (13604)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.57  % (13604)Refutation not found, incomplete strategy% (13604)------------------------------
% 1.43/0.57  % (13604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (13593)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.57  % (13604)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (13604)Memory used [KB]: 1663
% 1.43/0.57  % (13604)Time elapsed: 0.002 s
% 1.43/0.57  % (13604)------------------------------
% 1.43/0.57  % (13604)------------------------------
% 1.43/0.58  % (13597)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.43/0.58  % (13583)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.58  % (13580)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.58  % (13586)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.59  % (13601)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.59  % (13601)Refutation not found, incomplete strategy% (13601)------------------------------
% 1.43/0.59  % (13601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (13601)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.59  
% 1.43/0.59  % (13601)Memory used [KB]: 6268
% 1.43/0.59  % (13601)Time elapsed: 0.173 s
% 1.43/0.59  % (13601)------------------------------
% 1.43/0.59  % (13601)------------------------------
% 1.43/0.59  % (13593)Refutation not found, incomplete strategy% (13593)------------------------------
% 1.43/0.59  % (13593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (13593)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.59  
% 1.43/0.59  % (13593)Memory used [KB]: 1791
% 1.43/0.59  % (13593)Time elapsed: 0.174 s
% 1.43/0.59  % (13593)------------------------------
% 1.43/0.59  % (13593)------------------------------
% 1.43/0.62  % (13636)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.63  % (13597)Refutation found. Thanks to Tanya!
% 2.04/0.63  % SZS status Theorem for theBenchmark
% 2.04/0.63  % SZS output start Proof for theBenchmark
% 2.04/0.63  fof(f662,plain,(
% 2.04/0.63    $false),
% 2.04/0.63    inference(unit_resulting_resolution,[],[f304,f304,f84,f632])).
% 2.04/0.63  fof(f632,plain,(
% 2.04/0.63    ( ! [X23,X22] : (~r2_hidden(sK3,k1_enumset1(X22,X22,X23)) | sK3 != X22 | X22 != X23) )),
% 2.04/0.63    inference(backward_demodulation,[],[f586,f623])).
% 2.04/0.63  fof(f623,plain,(
% 2.04/0.63    sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.63    inference(trivial_inequality_removal,[],[f622])).
% 2.04/0.63  fof(f622,plain,(
% 2.04/0.63    sK3 != sK3 | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.63    inference(superposition,[],[f595,f462])).
% 2.04/0.63  fof(f462,plain,(
% 2.04/0.63    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k1_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.63    inference(superposition,[],[f412,f421])).
% 2.04/0.63  fof(f421,plain,(
% 2.04/0.63    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.63    inference(subsumption_resolution,[],[f415,f300])).
% 2.04/0.63  fof(f300,plain,(
% 2.04/0.63    sK3 != k7_mcart_1(sK0,sK1,sK2,sK3)),
% 2.04/0.63    inference(superposition,[],[f88,f291])).
% 2.04/0.63  fof(f291,plain,(
% 2.04/0.63    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 2.04/0.63    inference(subsumption_resolution,[],[f290,f34])).
% 2.04/0.63  fof(f34,plain,(
% 2.04/0.63    k1_xboole_0 != sK0),
% 2.04/0.63    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f19,plain,(
% 2.04/0.64    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f18,f17])).
% 2.04/0.64  fof(f17,plain,(
% 2.04/0.64    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f18,plain,(
% 2.04/0.64    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f13,plain,(
% 2.04/0.64    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.04/0.64    inference(ennf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,negated_conjecture,(
% 2.04/0.64    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.04/0.64    inference(negated_conjecture,[],[f11])).
% 2.04/0.64  fof(f11,conjecture,(
% 2.04/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 2.04/0.64  fof(f290,plain,(
% 2.04/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 2.04/0.64    inference(subsumption_resolution,[],[f289,f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    k1_xboole_0 != sK1),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f289,plain,(
% 2.04/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.04/0.64    inference(subsumption_resolution,[],[f288,f36])).
% 2.04/0.64  fof(f36,plain,(
% 2.04/0.64    k1_xboole_0 != sK2),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f288,plain,(
% 2.04/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 2.04/0.64    inference(resolution,[],[f77,f65])).
% 2.04/0.64  fof(f65,plain,(
% 2.04/0.64    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.04/0.64    inference(definition_unfolding,[],[f37,f47])).
% 2.04/0.64  fof(f47,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f6])).
% 2.04/0.64  fof(f6,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.04/0.64  fof(f37,plain,(
% 2.04/0.64    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f77,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(definition_unfolding,[],[f64,f48,f47])).
% 2.04/0.64  fof(f48,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f5])).
% 2.04/0.64  fof(f5,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.04/0.64  fof(f64,plain,(
% 2.04/0.64    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f16])).
% 2.04/0.64  fof(f16,plain,(
% 2.04/0.64    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.04/0.64    inference(ennf_transformation,[],[f9])).
% 2.04/0.64  fof(f9,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 2.04/0.64  fof(f88,plain,(
% 2.04/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 2.04/0.64    inference(backward_demodulation,[],[f78,f46])).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.04/0.64    inference(cnf_transformation,[],[f10])).
% 2.04/0.64  fof(f10,axiom,(
% 2.04/0.64    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.04/0.64  fof(f78,plain,(
% 2.04/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 2.04/0.64    inference(equality_resolution,[],[f40])).
% 2.04/0.64  fof(f40,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f14])).
% 2.04/0.64  fof(f14,plain,(
% 2.04/0.64    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 2.04/0.64    inference(ennf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 2.04/0.64  fof(f415,plain,(
% 2.04/0.64    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 2.04/0.64    inference(backward_demodulation,[],[f38,f411])).
% 2.04/0.64  fof(f411,plain,(
% 2.04/0.64    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.64    inference(superposition,[],[f46,f298])).
% 2.04/0.64  fof(f298,plain,(
% 2.04/0.64    k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) = k1_mcart_1(sK3)),
% 2.04/0.64    inference(superposition,[],[f45,f291])).
% 2.04/0.64  fof(f45,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f10])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 2.04/0.64    inference(cnf_transformation,[],[f19])).
% 2.04/0.64  fof(f412,plain,(
% 2.04/0.64    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.64    inference(superposition,[],[f45,f298])).
% 2.04/0.64  fof(f595,plain,(
% 2.04/0.64    sK3 != k2_mcart_1(k1_mcart_1(sK3))),
% 2.04/0.64    inference(equality_resolution,[],[f587])).
% 2.04/0.64  fof(f587,plain,(
% 2.04/0.64    ( ! [X0] : (k2_mcart_1(k1_mcart_1(sK3)) != X0 | sK3 != X0) )),
% 2.04/0.64    inference(resolution,[],[f585,f84])).
% 2.04/0.64  fof(f585,plain,(
% 2.04/0.64    ( ! [X21,X20] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X20,X20,X21)) | sK3 != X20 | X20 != X21) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f579,f119])).
% 2.04/0.64  fof(f119,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) != k1_xboole_0) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f118,f84])).
% 2.04/0.64  fof(f118,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) != k1_xboole_0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X1))) )),
% 2.04/0.64    inference(superposition,[],[f75,f98])).
% 2.04/0.64  fof(f98,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.04/0.64    inference(duplicate_literal_removal,[],[f95])).
% 2.04/0.64  fof(f95,plain,(
% 2.04/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.04/0.64    inference(resolution,[],[f91,f90])).
% 2.04/0.64  fof(f90,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r2_hidden(sK4(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.04/0.64    inference(resolution,[],[f81,f41])).
% 2.04/0.64  fof(f41,plain,(
% 2.04/0.64    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f21,plain,(
% 2.04/0.64    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 2.04/0.64  fof(f20,plain,(
% 2.04/0.64    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f15,plain,(
% 2.04/0.64    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.04/0.64    inference(ennf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 2.04/0.64  fof(f81,plain,(
% 2.04/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.04/0.64    inference(equality_resolution,[],[f50])).
% 2.04/0.64  fof(f50,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.04/0.64    inference(cnf_transformation,[],[f26])).
% 2.04/0.64  fof(f26,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 2.04/0.64  fof(f25,plain,(
% 2.04/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f24,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.64    inference(rectify,[],[f23])).
% 2.04/0.64  fof(f23,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.64    inference(flattening,[],[f22])).
% 2.04/0.64  fof(f22,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.04/0.64    inference(nnf_transformation,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.04/0.64  fof(f91,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.04/0.64    inference(resolution,[],[f82,f41])).
% 2.04/0.64  fof(f82,plain,(
% 2.04/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.04/0.64    inference(equality_resolution,[],[f49])).
% 2.04/0.64  fof(f49,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.04/0.64    inference(cnf_transformation,[],[f26])).
% 2.04/0.64  fof(f75,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f62,f44,f44])).
% 2.04/0.64  fof(f44,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f3])).
% 2.04/0.64  fof(f3,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.04/0.64  fof(f62,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f33])).
% 2.04/0.64  fof(f33,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.04/0.64    inference(flattening,[],[f32])).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.04/0.64    inference(nnf_transformation,[],[f4])).
% 2.04/0.64  fof(f4,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.04/0.64  fof(f579,plain,(
% 2.04/0.64    ( ! [X21,X20] : (sK3 != X20 | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X20,X20,X21)) | k1_xboole_0 = k1_enumset1(X20,X20,X21) | X20 != X21) )),
% 2.04/0.64    inference(superposition,[],[f416,f319])).
% 2.04/0.64  fof(f319,plain,(
% 2.04/0.64    ( ! [X0,X1] : (sK4(k1_enumset1(X0,X0,X1)) = X0 | X0 != X1) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f313,f119])).
% 2.04/0.64  fof(f313,plain,(
% 2.04/0.64    ( ! [X0,X1] : (X0 != X1 | sK4(k1_enumset1(X0,X0,X1)) = X0 | k1_enumset1(X0,X0,X1) = k1_xboole_0) )),
% 2.04/0.64    inference(equality_factoring,[],[f101])).
% 2.04/0.64  fof(f101,plain,(
% 2.04/0.64    ( ! [X4,X5] : (sK4(k1_enumset1(X4,X4,X5)) = X5 | sK4(k1_enumset1(X4,X4,X5)) = X4 | k1_xboole_0 = k1_enumset1(X4,X4,X5)) )),
% 2.04/0.64    inference(resolution,[],[f87,f41])).
% 2.04/0.64  fof(f87,plain,(
% 2.04/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.04/0.64    inference(equality_resolution,[],[f73])).
% 2.04/0.64  fof(f73,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 2.04/0.64    inference(definition_unfolding,[],[f55,f44])).
% 2.04/0.64  fof(f55,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.04/0.64    inference(cnf_transformation,[],[f31])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f29,f30])).
% 2.04/0.64  fof(f30,plain,(
% 2.04/0.64    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f29,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.04/0.64    inference(rectify,[],[f28])).
% 2.04/0.64  fof(f28,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.04/0.64    inference(flattening,[],[f27])).
% 2.04/0.64  fof(f27,plain,(
% 2.04/0.64    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.04/0.64    inference(nnf_transformation,[],[f2])).
% 2.04/0.64  fof(f2,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.04/0.64  fof(f416,plain,(
% 2.04/0.64    ( ! [X1] : (sK3 != sK4(X1) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),X1) | k1_xboole_0 = X1) )),
% 2.04/0.64    inference(backward_demodulation,[],[f294,f411])).
% 2.04/0.64  fof(f294,plain,(
% 2.04/0.64    ( ! [X1] : (sK3 != sK4(X1) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),X1) | k1_xboole_0 = X1) )),
% 2.04/0.64    inference(superposition,[],[f66,f291])).
% 2.04/0.64  fof(f66,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(definition_unfolding,[],[f43,f48])).
% 2.04/0.64  fof(f43,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f586,plain,(
% 2.04/0.64    ( ! [X23,X22] : (sK3 != X22 | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X22,X22,X23)) | X22 != X23) )),
% 2.04/0.64    inference(subsumption_resolution,[],[f580,f119])).
% 2.04/0.64  fof(f580,plain,(
% 2.04/0.64    ( ! [X23,X22] : (sK3 != X22 | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X22,X22,X23)) | k1_xboole_0 = k1_enumset1(X22,X22,X23) | X22 != X23) )),
% 2.04/0.64    inference(superposition,[],[f422,f319])).
% 2.04/0.64  fof(f422,plain,(
% 2.04/0.64    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(backward_demodulation,[],[f293,f412])).
% 2.04/0.64  fof(f293,plain,(
% 2.04/0.64    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(superposition,[],[f67,f291])).
% 2.04/0.64  fof(f67,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(definition_unfolding,[],[f42,f48])).
% 2.04/0.64  fof(f42,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f84,plain,(
% 2.04/0.64    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 2.04/0.64    inference(equality_resolution,[],[f83])).
% 2.04/0.64  fof(f83,plain,(
% 2.04/0.64    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 2.04/0.64    inference(equality_resolution,[],[f71])).
% 2.04/0.64  fof(f71,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.04/0.64    inference(definition_unfolding,[],[f57,f44])).
% 2.04/0.64  fof(f57,plain,(
% 2.04/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.04/0.64    inference(cnf_transformation,[],[f31])).
% 2.04/0.64  fof(f304,plain,(
% 2.04/0.64    sK3 = k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3))),
% 2.04/0.64    inference(backward_demodulation,[],[f303,f298])).
% 2.04/0.64  fof(f303,plain,(
% 2.04/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))),
% 2.04/0.64    inference(backward_demodulation,[],[f291,f297])).
% 2.04/0.64  fof(f297,plain,(
% 2.04/0.64    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 2.04/0.64    inference(superposition,[],[f46,f291])).
% 2.04/0.64  % SZS output end Proof for theBenchmark
% 2.04/0.64  % (13597)------------------------------
% 2.04/0.64  % (13597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (13597)Termination reason: Refutation
% 2.04/0.64  
% 2.04/0.64  % (13597)Memory used [KB]: 7036
% 2.04/0.64  % (13597)Time elapsed: 0.194 s
% 2.04/0.64  % (13597)------------------------------
% 2.04/0.64  % (13597)------------------------------
% 2.04/0.64  % (13574)Success in time 0.277 s
%------------------------------------------------------------------------------
