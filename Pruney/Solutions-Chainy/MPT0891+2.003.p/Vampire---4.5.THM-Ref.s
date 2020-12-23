%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:06 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  144 (1136 expanded)
%              Number of leaves         :   22 ( 367 expanded)
%              Depth                    :   24
%              Number of atoms          :  570 (5862 expanded)
%              Number of equality atoms :  361 (4108 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f180,f112,f398,f559])).

fof(f559,plain,(
    ! [X1] :
      ( sK3 != sK4(X1)
      | ~ r2_hidden(sK3,X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f436,f558])).

fof(f558,plain,(
    sK3 = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f368,f557])).

fof(f557,plain,(
    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f556,f441])).

fof(f441,plain,(
    sK3 != k2_mcart_1(sK3) ),
    inference(superposition,[],[f124,f431])).

fof(f431,plain,(
    sK3 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f430,f395])).

fof(f395,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f394,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f394,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f393,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f393,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f392,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f392,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f108,f89])).

fof(f89,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f48,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f66])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f430,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f429,f368])).

fof(f429,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f428,f324])).

fof(f324,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f323,f45])).

fof(f323,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f322,f46])).

fof(f322,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f321,f47])).

fof(f321,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f106,f89])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f66])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f428,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f427,f45])).

fof(f427,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f426,f46])).

fof(f426,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f425,f47])).

fof(f425,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f105,f89])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f65,f66])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f124,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(backward_demodulation,[],[f109,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f109,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f556,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(trivial_inequality_removal,[],[f555])).

fof(f555,plain,
    ( sK3 != sK3
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(superposition,[],[f526,f397])).

fof(f397,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(backward_demodulation,[],[f325,f395])).

fof(f325,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f324,f49])).

fof(f49,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f526,plain,(
    sK3 != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(resolution,[],[f515,f112])).

fof(f515,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X0,X0,X0))
      | sK3 != X0 ) ),
    inference(subsumption_resolution,[],[f512,f180])).

fof(f512,plain,(
    ! [X0] :
      ( sK3 != X0
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f435,f398])).

fof(f435,plain,(
    ! [X0] :
      ( sK3 != sK4(X0)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f91,f431])).

fof(f91,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f55,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).

fof(f27,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f368,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f367,f45])).

fof(f367,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f366,f46])).

fof(f366,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f365,f47])).

fof(f365,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f107,f89])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f66])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f436,plain,(
    ! [X1] :
      ( sK3 != sK4(X1)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f90,f431])).

fof(f90,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f56,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f398,plain,(
    ! [X0] : sK4(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(resolution,[],[f320,f112])).

fof(f320,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(k1_enumset1(X8,X8,X8)),k1_enumset1(X9,X9,X9))
      | X8 = X9 ) ),
    inference(subsumption_resolution,[],[f308,f180])).

fof(f308,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK4(k1_enumset1(X8,X8,X8)),k1_enumset1(X9,X9,X9))
      | X8 = X9
      | k1_xboole_0 = k1_enumset1(X8,X8,X8) ) ),
    inference(resolution,[],[f303,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f303,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(X17,k1_enumset1(X16,X16,X16))
      | ~ r2_hidden(X17,k1_enumset1(X15,X15,X15))
      | X15 = X16 ) ),
    inference(subsumption_resolution,[],[f302,f147])).

fof(f147,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f103,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f74,f57,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f302,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,k1_enumset1(X16,X16,X16))
      | ~ r2_hidden(X17,k1_enumset1(X15,X15,X15))
      | X15 = X16 ) ),
    inference(forward_demodulation,[],[f294,f155])).

fof(f155,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f151,f54])).

fof(f151,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k4_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f150,f50])).

fof(f150,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) ),
    inference(resolution,[],[f147,f115])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f294,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(X17,k4_xboole_0(k1_enumset1(X15,X15,X15),k1_enumset1(X15,X15,X15)))
      | ~ r2_hidden(X17,k1_enumset1(X16,X16,X16))
      | ~ r2_hidden(X17,k1_enumset1(X15,X15,X15))
      | X15 = X16 ) ),
    inference(superposition,[],[f114,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f214,f113])).

fof(f113,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f214,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(factoring,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f75,f57,f57])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f69,f58])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f88])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f180,plain,(
    ! [X4,X5] : k1_xboole_0 != k1_enumset1(X4,X4,X5) ),
    inference(subsumption_resolution,[],[f175,f120])).

fof(f120,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK7(X0,X1,X2,X3) != X2
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X2
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X0
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
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
     => ( ( ( sK7(X0,X1,X2,X3) != X2
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X2
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X0
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f175,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k1_enumset1(X4,X4,X5)
      | ~ r2_hidden(X4,k1_enumset1(X4,X4,X5)) ) ),
    inference(superposition,[],[f104,f155])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f73,f57,f57])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (17243)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (17215)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.50  % (17243)Refutation not found, incomplete strategy% (17243)------------------------------
% 0.22/0.50  % (17243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17243)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (17243)Memory used [KB]: 1663
% 0.22/0.50  % (17243)Time elapsed: 0.004 s
% 0.22/0.50  % (17243)------------------------------
% 0.22/0.50  % (17243)------------------------------
% 0.22/0.51  % (17217)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (17214)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (17231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (17231)Refutation not found, incomplete strategy% (17231)------------------------------
% 0.22/0.53  % (17231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17231)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17231)Memory used [KB]: 1791
% 0.22/0.53  % (17231)Time elapsed: 0.106 s
% 0.22/0.53  % (17231)------------------------------
% 0.22/0.53  % (17231)------------------------------
% 0.22/0.53  % (17224)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (17236)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (17215)Refutation not found, incomplete strategy% (17215)------------------------------
% 0.22/0.54  % (17215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17215)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17215)Memory used [KB]: 2046
% 0.22/0.54  % (17215)Time elapsed: 0.110 s
% 0.22/0.54  % (17215)------------------------------
% 0.22/0.54  % (17215)------------------------------
% 0.22/0.54  % (17216)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (17219)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.55  % (17218)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.55  % (17235)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.56  % (17223)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.56  % (17233)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.56  % (17220)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.56  % (17240)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (17230)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.56  % (17230)Refutation not found, incomplete strategy% (17230)------------------------------
% 1.54/0.56  % (17230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (17230)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (17230)Memory used [KB]: 10746
% 1.54/0.56  % (17230)Time elapsed: 0.144 s
% 1.54/0.56  % (17230)------------------------------
% 1.54/0.56  % (17230)------------------------------
% 1.54/0.56  % (17227)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.54/0.57  % (17239)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.54/0.57  % (17237)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.57  % (17228)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.54/0.57  % (17242)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.57  % (17238)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.54/0.57  % (17221)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.54/0.57  % (17229)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.57  % (17232)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.54/0.58  % (17232)Refutation not found, incomplete strategy% (17232)------------------------------
% 1.54/0.58  % (17232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (17232)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (17232)Memory used [KB]: 1791
% 1.54/0.58  % (17232)Time elapsed: 0.157 s
% 1.54/0.58  % (17232)------------------------------
% 1.54/0.58  % (17232)------------------------------
% 1.54/0.58  % (17226)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.58  % (17241)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.54/0.58  % (17238)Refutation not found, incomplete strategy% (17238)------------------------------
% 1.54/0.58  % (17238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (17238)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (17238)Memory used [KB]: 10746
% 1.54/0.58  % (17238)Time elapsed: 0.155 s
% 1.54/0.58  % (17238)------------------------------
% 1.54/0.58  % (17238)------------------------------
% 1.54/0.58  % (17226)Refutation not found, incomplete strategy% (17226)------------------------------
% 1.54/0.58  % (17226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (17226)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (17226)Memory used [KB]: 10746
% 1.54/0.58  % (17226)Time elapsed: 0.170 s
% 1.54/0.58  % (17226)------------------------------
% 1.54/0.58  % (17226)------------------------------
% 1.54/0.58  % (17222)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.54/0.58  % (17225)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.54/0.58  % (17240)Refutation not found, incomplete strategy% (17240)------------------------------
% 1.54/0.58  % (17240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (17240)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (17240)Memory used [KB]: 6268
% 1.54/0.58  % (17240)Time elapsed: 0.149 s
% 1.54/0.58  % (17240)------------------------------
% 1.54/0.58  % (17240)------------------------------
% 1.54/0.59  % (17234)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.59  % (17228)Refutation not found, incomplete strategy% (17228)------------------------------
% 1.54/0.59  % (17228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (17228)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (17228)Memory used [KB]: 1791
% 1.54/0.59  % (17228)Time elapsed: 0.149 s
% 1.54/0.59  % (17228)------------------------------
% 1.54/0.59  % (17228)------------------------------
% 1.54/0.59  % (17236)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.59  % SZS output start Proof for theBenchmark
% 1.54/0.59  fof(f598,plain,(
% 1.54/0.59    $false),
% 1.54/0.59    inference(unit_resulting_resolution,[],[f180,f112,f398,f559])).
% 1.54/0.59  fof(f559,plain,(
% 1.54/0.59    ( ! [X1] : (sK3 != sK4(X1) | ~r2_hidden(sK3,X1) | k1_xboole_0 = X1) )),
% 1.54/0.59    inference(backward_demodulation,[],[f436,f558])).
% 1.54/0.59  fof(f558,plain,(
% 1.54/0.59    sK3 = k2_mcart_1(k1_mcart_1(sK3))),
% 1.54/0.59    inference(backward_demodulation,[],[f368,f557])).
% 1.54/0.59  fof(f557,plain,(
% 1.54/0.59    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 1.54/0.59    inference(subsumption_resolution,[],[f556,f441])).
% 1.54/0.59  fof(f441,plain,(
% 1.54/0.59    sK3 != k2_mcart_1(sK3)),
% 1.54/0.59    inference(superposition,[],[f124,f431])).
% 1.54/0.59  fof(f431,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(sK3))),
% 1.54/0.59    inference(forward_demodulation,[],[f430,f395])).
% 1.54/0.59  fof(f395,plain,(
% 1.54/0.59    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.54/0.59    inference(subsumption_resolution,[],[f394,f45])).
% 1.54/0.59  fof(f45,plain,(
% 1.54/0.59    k1_xboole_0 != sK0),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f26,plain,(
% 1.54/0.59    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24])).
% 1.54/0.59  fof(f24,plain,(
% 1.54/0.59    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f25,plain,(
% 1.54/0.59    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f18,plain,(
% 1.54/0.59    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.54/0.59    inference(ennf_transformation,[],[f17])).
% 1.54/0.59  fof(f17,negated_conjecture,(
% 1.54/0.59    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.54/0.59    inference(negated_conjecture,[],[f16])).
% 1.54/0.59  fof(f16,conjecture,(
% 1.54/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.54/0.59  fof(f394,plain,(
% 1.54/0.59    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f393,f46])).
% 1.54/0.59  fof(f46,plain,(
% 1.54/0.59    k1_xboole_0 != sK1),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f393,plain,(
% 1.54/0.59    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f392,f47])).
% 1.54/0.59  fof(f47,plain,(
% 1.54/0.59    k1_xboole_0 != sK2),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f392,plain,(
% 1.54/0.59    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(resolution,[],[f108,f89])).
% 1.54/0.59  fof(f89,plain,(
% 1.54/0.59    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.54/0.59    inference(definition_unfolding,[],[f48,f66])).
% 1.54/0.59  fof(f66,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f10])).
% 1.54/0.59  fof(f10,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.54/0.59  fof(f48,plain,(
% 1.54/0.59    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f108,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f77,f66])).
% 1.54/0.59  fof(f77,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f22,plain,(
% 1.54/0.59    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.54/0.59    inference(ennf_transformation,[],[f14])).
% 1.54/0.59  fof(f14,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.54/0.59  fof(f430,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3))),k2_mcart_1(sK3))),
% 1.54/0.59    inference(forward_demodulation,[],[f429,f368])).
% 1.54/0.59  fof(f429,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))),
% 1.54/0.59    inference(forward_demodulation,[],[f428,f324])).
% 1.54/0.59  fof(f324,plain,(
% 1.54/0.59    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 1.54/0.59    inference(subsumption_resolution,[],[f323,f45])).
% 1.54/0.59  fof(f323,plain,(
% 1.54/0.59    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f322,f46])).
% 1.54/0.59  fof(f322,plain,(
% 1.54/0.59    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f321,f47])).
% 1.54/0.59  fof(f321,plain,(
% 1.54/0.59    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(resolution,[],[f106,f89])).
% 1.54/0.59  fof(f106,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f79,f66])).
% 1.54/0.59  fof(f79,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f428,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.54/0.59    inference(subsumption_resolution,[],[f427,f45])).
% 1.54/0.59  fof(f427,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f426,f46])).
% 1.54/0.59  fof(f426,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f425,f47])).
% 1.54/0.59  fof(f425,plain,(
% 1.54/0.59    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(resolution,[],[f105,f89])).
% 1.54/0.59  fof(f105,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f76,f65,f66])).
% 1.54/0.59  fof(f65,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f9])).
% 1.54/0.59  fof(f9,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.54/0.59  fof(f76,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f21])).
% 1.54/0.59  fof(f21,plain,(
% 1.54/0.59    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.54/0.59    inference(ennf_transformation,[],[f13])).
% 1.54/0.59  fof(f13,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.54/0.59  fof(f124,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.54/0.59    inference(backward_demodulation,[],[f109,f60])).
% 1.54/0.59  fof(f60,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.54/0.59    inference(cnf_transformation,[],[f15])).
% 1.54/0.59  fof(f15,axiom,(
% 1.54/0.59    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.54/0.59  fof(f109,plain,(
% 1.54/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.54/0.59    inference(equality_resolution,[],[f53])).
% 1.54/0.59  fof(f53,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f19])).
% 1.54/0.59  fof(f19,plain,(
% 1.54/0.59    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.54/0.59    inference(ennf_transformation,[],[f11])).
% 1.54/0.59  fof(f11,axiom,(
% 1.54/0.59    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.54/0.59  fof(f556,plain,(
% 1.54/0.59    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3)),
% 1.54/0.59    inference(trivial_inequality_removal,[],[f555])).
% 1.54/0.59  fof(f555,plain,(
% 1.54/0.59    sK3 != sK3 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3)),
% 1.54/0.59    inference(superposition,[],[f526,f397])).
% 1.54/0.59  fof(f397,plain,(
% 1.54/0.59    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3)),
% 1.54/0.59    inference(backward_demodulation,[],[f325,f395])).
% 1.54/0.59  fof(f325,plain,(
% 1.54/0.59    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.54/0.59    inference(superposition,[],[f324,f49])).
% 1.54/0.59  fof(f49,plain,(
% 1.54/0.59    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f526,plain,(
% 1.54/0.59    sK3 != k1_mcart_1(k1_mcart_1(sK3))),
% 1.54/0.59    inference(resolution,[],[f515,f112])).
% 1.54/0.59  fof(f515,plain,(
% 1.54/0.59    ( ! [X0] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X0,X0,X0)) | sK3 != X0) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f512,f180])).
% 1.54/0.59  fof(f512,plain,(
% 1.54/0.59    ( ! [X0] : (sK3 != X0 | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 1.54/0.59    inference(superposition,[],[f435,f398])).
% 1.54/0.59  fof(f435,plain,(
% 1.54/0.59    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK3)),X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(superposition,[],[f91,f431])).
% 1.54/0.59  fof(f91,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f55,f65])).
% 1.54/0.59  fof(f55,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f28])).
% 1.54/0.59  fof(f28,plain,(
% 1.54/0.59    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).
% 1.54/0.59  fof(f27,plain,(
% 1.54/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f20,plain,(
% 1.54/0.59    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.54/0.59    inference(ennf_transformation,[],[f12])).
% 1.54/0.59  fof(f12,axiom,(
% 1.54/0.59    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.54/0.59  fof(f368,plain,(
% 1.54/0.59    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.54/0.59    inference(subsumption_resolution,[],[f367,f45])).
% 1.54/0.59  fof(f367,plain,(
% 1.54/0.59    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f366,f46])).
% 1.54/0.59  fof(f366,plain,(
% 1.54/0.59    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(subsumption_resolution,[],[f365,f47])).
% 1.54/0.59  fof(f365,plain,(
% 1.54/0.59    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.54/0.59    inference(resolution,[],[f107,f89])).
% 1.54/0.59  fof(f107,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f78,f66])).
% 1.54/0.59  fof(f78,plain,(
% 1.54/0.59    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f22])).
% 1.54/0.59  fof(f436,plain,(
% 1.54/0.59    ( ! [X1] : (sK3 != sK4(X1) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK3)),X1) | k1_xboole_0 = X1) )),
% 1.54/0.59    inference(superposition,[],[f90,f431])).
% 1.54/0.59  fof(f90,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(definition_unfolding,[],[f56,f65])).
% 1.54/0.59  fof(f56,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f28])).
% 1.54/0.59  fof(f398,plain,(
% 1.54/0.59    ( ! [X0] : (sK4(k1_enumset1(X0,X0,X0)) = X0) )),
% 1.54/0.59    inference(resolution,[],[f320,f112])).
% 1.54/0.59  fof(f320,plain,(
% 1.54/0.59    ( ! [X8,X9] : (~r2_hidden(sK4(k1_enumset1(X8,X8,X8)),k1_enumset1(X9,X9,X9)) | X8 = X9) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f308,f180])).
% 1.54/0.59  fof(f308,plain,(
% 1.54/0.59    ( ! [X8,X9] : (~r2_hidden(sK4(k1_enumset1(X8,X8,X8)),k1_enumset1(X9,X9,X9)) | X8 = X9 | k1_xboole_0 = k1_enumset1(X8,X8,X8)) )),
% 1.54/0.59    inference(resolution,[],[f303,f54])).
% 1.54/0.59  fof(f54,plain,(
% 1.54/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f28])).
% 1.54/0.59  fof(f303,plain,(
% 1.54/0.59    ( ! [X17,X15,X16] : (~r2_hidden(X17,k1_enumset1(X16,X16,X16)) | ~r2_hidden(X17,k1_enumset1(X15,X15,X15)) | X15 = X16) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f302,f147])).
% 1.54/0.59  fof(f147,plain,(
% 1.54/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.54/0.59    inference(trivial_inequality_removal,[],[f146])).
% 1.54/0.59  fof(f146,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.54/0.59    inference(superposition,[],[f103,f50])).
% 1.54/0.59  fof(f50,plain,(
% 1.54/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.59    inference(cnf_transformation,[],[f2])).
% 1.54/0.59  fof(f2,axiom,(
% 1.54/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.54/0.59  fof(f103,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.54/0.59    inference(definition_unfolding,[],[f74,f57,f57])).
% 1.54/0.59  fof(f57,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f7])).
% 1.54/0.59  fof(f7,axiom,(
% 1.54/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.59  fof(f74,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f39])).
% 1.54/0.59  fof(f39,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.54/0.59    inference(flattening,[],[f38])).
% 1.54/0.59  fof(f38,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.54/0.59    inference(nnf_transformation,[],[f8])).
% 1.54/0.59  fof(f8,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.54/0.59  fof(f302,plain,(
% 1.54/0.59    ( ! [X17,X15,X16] : (r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,k1_enumset1(X16,X16,X16)) | ~r2_hidden(X17,k1_enumset1(X15,X15,X15)) | X15 = X16) )),
% 1.54/0.59    inference(forward_demodulation,[],[f294,f155])).
% 1.54/0.59  fof(f155,plain,(
% 1.54/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.54/0.59    inference(resolution,[],[f151,f54])).
% 1.54/0.59  fof(f151,plain,(
% 1.54/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k4_xboole_0(X3,X3))) )),
% 1.54/0.59    inference(forward_demodulation,[],[f150,f50])).
% 1.54/0.59  fof(f150,plain,(
% 1.54/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)))) )),
% 1.54/0.59    inference(resolution,[],[f147,f115])).
% 1.54/0.59  fof(f115,plain,(
% 1.54/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.54/0.59    inference(equality_resolution,[],[f100])).
% 1.54/0.59  fof(f100,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.54/0.59    inference(definition_unfolding,[],[f68,f58])).
% 1.54/0.59  fof(f58,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.59    inference(cnf_transformation,[],[f3])).
% 1.54/0.59  fof(f3,axiom,(
% 1.54/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.59  fof(f68,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.54/0.59    inference(cnf_transformation,[],[f37])).
% 1.54/0.59  fof(f37,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.54/0.59  fof(f36,plain,(
% 1.54/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f35,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.54/0.59    inference(rectify,[],[f34])).
% 1.54/0.59  fof(f34,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.54/0.59    inference(flattening,[],[f33])).
% 1.54/0.59  fof(f33,plain,(
% 1.54/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.54/0.59    inference(nnf_transformation,[],[f1])).
% 1.54/0.59  fof(f1,axiom,(
% 1.54/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.54/0.59  fof(f294,plain,(
% 1.54/0.59    ( ! [X17,X15,X16] : (r2_hidden(X17,k4_xboole_0(k1_enumset1(X15,X15,X15),k1_enumset1(X15,X15,X15))) | ~r2_hidden(X17,k1_enumset1(X16,X16,X16)) | ~r2_hidden(X17,k1_enumset1(X15,X15,X15)) | X15 = X16) )),
% 1.54/0.59    inference(superposition,[],[f114,f215])).
% 1.54/0.59  fof(f215,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 1.54/0.59    inference(resolution,[],[f214,f113])).
% 1.54/0.59  fof(f113,plain,(
% 1.54/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 1.54/0.59    inference(equality_resolution,[],[f95])).
% 1.54/0.59  fof(f95,plain,(
% 1.54/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.54/0.59    inference(definition_unfolding,[],[f61,f88])).
% 1.54/0.59  fof(f88,plain,(
% 1.54/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.54/0.59    inference(definition_unfolding,[],[f51,f57])).
% 1.54/0.59  fof(f51,plain,(
% 1.54/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f6])).
% 1.54/0.59  fof(f6,axiom,(
% 1.54/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.59  fof(f61,plain,(
% 1.54/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.59    inference(cnf_transformation,[],[f32])).
% 1.54/0.59  fof(f32,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.54/0.59  fof(f31,plain,(
% 1.54/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f30,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(rectify,[],[f29])).
% 1.54/0.59  fof(f29,plain,(
% 1.54/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.54/0.59    inference(nnf_transformation,[],[f5])).
% 1.54/0.59  fof(f5,axiom,(
% 1.54/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.54/0.59  fof(f214,plain,(
% 1.54/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 1.54/0.59    inference(factoring,[],[f102])).
% 1.54/0.59  fof(f102,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.54/0.59    inference(definition_unfolding,[],[f75,f57,f57])).
% 1.54/0.59  fof(f75,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f39])).
% 1.54/0.59  fof(f114,plain,(
% 1.54/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f99])).
% 1.54/0.59  fof(f99,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.54/0.59    inference(definition_unfolding,[],[f69,f58])).
% 1.54/0.59  fof(f69,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.54/0.59    inference(cnf_transformation,[],[f37])).
% 1.54/0.59  fof(f112,plain,(
% 1.54/0.59    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 1.54/0.59    inference(equality_resolution,[],[f111])).
% 1.54/0.59  fof(f111,plain,(
% 1.54/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 1.54/0.59    inference(equality_resolution,[],[f94])).
% 1.54/0.59  fof(f94,plain,(
% 1.54/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 1.54/0.59    inference(definition_unfolding,[],[f62,f88])).
% 1.54/0.59  fof(f62,plain,(
% 1.54/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.54/0.59    inference(cnf_transformation,[],[f32])).
% 1.54/0.59  fof(f180,plain,(
% 1.54/0.59    ( ! [X4,X5] : (k1_xboole_0 != k1_enumset1(X4,X4,X5)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f175,f120])).
% 1.54/0.59  fof(f120,plain,(
% 1.54/0.59    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 1.54/0.59    inference(equality_resolution,[],[f119])).
% 1.54/0.59  fof(f119,plain,(
% 1.54/0.59    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 1.54/0.59    inference(equality_resolution,[],[f82])).
% 1.54/0.59  fof(f82,plain,(
% 1.54/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.54/0.59    inference(cnf_transformation,[],[f44])).
% 1.54/0.59  fof(f44,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK7(X0,X1,X2,X3) != X2 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X2 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X0 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 1.54/0.59  fof(f43,plain,(
% 1.54/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X2 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X2 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X0 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f42,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.54/0.59    inference(rectify,[],[f41])).
% 1.54/0.59  fof(f41,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.54/0.59    inference(flattening,[],[f40])).
% 1.54/0.59  fof(f40,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.54/0.59    inference(nnf_transformation,[],[f23])).
% 1.54/0.59  fof(f23,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.54/0.59    inference(ennf_transformation,[],[f4])).
% 1.54/0.59  fof(f4,axiom,(
% 1.54/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.54/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.54/0.59  fof(f175,plain,(
% 1.54/0.59    ( ! [X4,X5] : (k1_xboole_0 != k1_enumset1(X4,X4,X5) | ~r2_hidden(X4,k1_enumset1(X4,X4,X5))) )),
% 1.54/0.59    inference(superposition,[],[f104,f155])).
% 1.54/0.59  fof(f104,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.54/0.59    inference(definition_unfolding,[],[f73,f57,f57])).
% 1.54/0.59  fof(f73,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f39])).
% 1.54/0.59  % SZS output end Proof for theBenchmark
% 1.54/0.59  % (17236)------------------------------
% 1.54/0.59  % (17236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (17236)Termination reason: Refutation
% 1.54/0.59  
% 1.54/0.59  % (17236)Memory used [KB]: 7036
% 1.54/0.59  % (17236)Time elapsed: 0.153 s
% 1.54/0.59  % (17236)------------------------------
% 1.54/0.59  % (17236)------------------------------
% 1.54/0.60  % (17241)Refutation not found, incomplete strategy% (17241)------------------------------
% 1.54/0.60  % (17241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (17241)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (17241)Memory used [KB]: 6268
% 1.54/0.60  % (17241)Time elapsed: 0.164 s
% 1.54/0.60  % (17241)------------------------------
% 1.54/0.60  % (17241)------------------------------
% 1.54/0.61  % (17213)Success in time 0.245 s
%------------------------------------------------------------------------------
