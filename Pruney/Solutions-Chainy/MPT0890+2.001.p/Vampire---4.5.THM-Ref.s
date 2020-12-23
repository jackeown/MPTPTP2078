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
% DateTime   : Thu Dec  3 12:59:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 400 expanded)
%              Number of leaves         :   10 ( 152 expanded)
%              Depth                    :   20
%              Number of atoms          :  260 (2462 expanded)
%              Number of equality atoms :  207 (1979 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
      | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
      | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3)
              | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
              | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(sK0,sK1,sK2,X3)
            | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(sK0,sK1,sK2,X3)
            | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(sK0,sK1,sK2,X3) )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X3] :
        ( ( k2_mcart_1(X3) != k7_mcart_1(sK0,sK1,sK2,X3)
          | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(sK0,sK1,sK2,X3)
          | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(sK0,sK1,sK2,X3) )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
        | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
        | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3)
            | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                  & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                  & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f105,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f104,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f103,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f102,f101])).

fof(f101,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f96,f100])).

fof(f100,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f99,f18])).

fof(f99,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f98,f19])).

fof(f98,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f97,f20])).

fof(f97,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f75,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5))
      | k2_mcart_1(k1_mcart_1(sK3)) = k6_mcart_1(X3,X4,X5,sK3)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3 ) ),
    inference(backward_demodulation,[],[f48,f71])).

fof(f71,plain,(
    k2_mcart_1(k1_mcart_1(sK3)) = sK5(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f27,f54])).

fof(f54,plain,(
    k1_mcart_1(sK3) = k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f26,f46])).

fof(f46,plain,(
    sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f45,f18])).

fof(f45,plain,
    ( sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f44,plain,
    ( sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f40,f20])).

fof(f40,plain,
    ( sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f36,f21])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k4_tarski(k4_tarski(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)),sK6(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK6(X0,X1,X2,X3),X2)
            & m1_subset_1(sK5(X0,X1,X2,X3),X1)
            & m1_subset_1(sK4(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f16,f15,f14])).

fof(f14,plain,(
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
                ( k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK6(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f26,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5))
      | sK5(sK0,sK1,sK2,sK3) = k6_mcart_1(X3,X4,X5,sK3)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f38,f46])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = X5
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4,X5,X6] :
              ( ( k7_mcart_1(X0,X1,X2,X3) = X6
                & k6_mcart_1(X0,X1,X2,X3) = X5
                & k5_mcart_1(X0,X1,X2,X3) = X4 )
              | k3_mcart_1(X4,X5,X6) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

fof(f96,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f22,f95])).

fof(f95,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f94,f18])).

fof(f94,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f20])).

fof(f92,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f56,f21])).

fof(f56,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8))
      | k2_mcart_1(sK3) = k7_mcart_1(X6,X7,X8,sK3)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(backward_demodulation,[],[f49,f53])).

fof(f53,plain,(
    k2_mcart_1(sK3) = sK6(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f27,f46])).

fof(f49,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8))
      | sK6(sK0,sK1,sK2,sK3) = k7_mcart_1(X6,X7,X8,sK3)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(superposition,[],[f37,f46])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f102,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f78,f21])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | k1_mcart_1(k1_mcart_1(sK3)) = k5_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f47,f72])).

fof(f72,plain,(
    k1_mcart_1(k1_mcart_1(sK3)) = sK4(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f26,f54])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2))
      | sK4(sK0,sK1,sK2,sK3) = k5_mcart_1(X0,X1,X2,sK3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f39,f46])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(X4,X5,X6) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:59 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.56  % (30539)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (30563)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (30534)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (30539)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f106,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(subsumption_resolution,[],[f105,f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    k1_xboole_0 != sK0),
% 0.22/0.60    inference(cnf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,plain,(
% 0.22/0.60    ((k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f12,f11])).
% 0.22/0.60  fof(f11,plain,(
% 0.22/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3) | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3)) | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k2_mcart_1(X3) != k7_mcart_1(sK0,sK1,sK2,X3) | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(sK0,sK1,sK2,X3) | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(sK0,sK1,sK2,X3)) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f12,plain,(
% 0.22/0.60    ? [X3] : ((k2_mcart_1(X3) != k7_mcart_1(sK0,sK1,sK2,X3) | k2_mcart_1(k1_mcart_1(X3)) != k6_mcart_1(sK0,sK1,sK2,X3) | k1_mcart_1(k1_mcart_1(X3)) != k5_mcart_1(sK0,sK1,sK2,X3)) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f8,plain,(
% 0.22/0.60    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3) | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3)) | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.60    inference(ennf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.60    inference(negated_conjecture,[],[f6])).
% 0.22/0.60  fof(f6,conjecture,(
% 0.22/0.60    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.60  fof(f105,plain,(
% 0.22/0.60    k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f104,f19])).
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    k1_xboole_0 != sK1),
% 0.22/0.60    inference(cnf_transformation,[],[f13])).
% 0.22/0.60  fof(f104,plain,(
% 0.22/0.60    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f103,f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    k1_xboole_0 != sK2),
% 0.22/0.60    inference(cnf_transformation,[],[f13])).
% 0.22/0.60  fof(f103,plain,(
% 0.22/0.60    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f102,f101])).
% 0.22/0.60  fof(f101,plain,(
% 0.22/0.60    k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.60    inference(subsumption_resolution,[],[f96,f100])).
% 0.22/0.60  fof(f100,plain,(
% 0.22/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.60    inference(subsumption_resolution,[],[f99,f18])).
% 0.22/0.60  fof(f99,plain,(
% 0.22/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f98,f19])).
% 0.22/0.60  fof(f98,plain,(
% 0.22/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f97,f20])).
% 0.22/0.60  fof(f97,plain,(
% 0.22/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(resolution,[],[f75,f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.60    inference(cnf_transformation,[],[f13])).
% 0.22/0.60  fof(f75,plain,(
% 0.22/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5)) | k2_mcart_1(k1_mcart_1(sK3)) = k6_mcart_1(X3,X4,X5,sK3) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) )),
% 0.22/0.60    inference(backward_demodulation,[],[f48,f71])).
% 0.22/0.60  fof(f71,plain,(
% 0.22/0.60    k2_mcart_1(k1_mcart_1(sK3)) = sK5(sK0,sK1,sK2,sK3)),
% 0.22/0.60    inference(superposition,[],[f27,f54])).
% 0.22/0.60  fof(f54,plain,(
% 0.22/0.60    k1_mcart_1(sK3) = k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3))),
% 0.22/0.60    inference(superposition,[],[f26,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3))),
% 0.22/0.60    inference(subsumption_resolution,[],[f45,f18])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f44,f19])).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f40,f20])).
% 0.22/0.60  fof(f40,plain,(
% 0.22/0.60    sK3 = k4_tarski(k4_tarski(sK4(sK0,sK1,sK2,sK3),sK5(sK0,sK1,sK2,sK3)),sK6(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(resolution,[],[f36,f21])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k4_tarski(k4_tarski(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3)),sK6(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 & m1_subset_1(sK6(X0,X1,X2,X3),X2)) & m1_subset_1(sK5(X0,X1,X2,X3),X1)) & m1_subset_1(sK4(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f16,f15,f14])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4(X0,X1,X2,X3),X0)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK5(X0,X1,X2,X3),X1)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK4(X0,X1,X2,X3),sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)) = X3 & m1_subset_1(sK6(X0,X1,X2,X3),X2)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f10,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f5])).
% 0.22/0.60  fof(f48,plain,(
% 0.22/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k3_zfmisc_1(X3,X4,X5)) | sK5(sK0,sK1,sK2,sK3) = k6_mcart_1(X3,X4,X5,sK3) | k1_xboole_0 = X5 | k1_xboole_0 = X4 | k1_xboole_0 = X3) )),
% 0.22/0.60    inference(superposition,[],[f38,f46])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(equality_resolution,[],[f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f24,f32])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = X5 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (! [X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.60    inference(ennf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ~(? [X3] : (? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).
% 0.22/0.60  fof(f96,plain,(
% 0.22/0.60    k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.60    inference(subsumption_resolution,[],[f22,f95])).
% 0.22/0.60  fof(f95,plain,(
% 0.22/0.60    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 0.22/0.60    inference(subsumption_resolution,[],[f94,f18])).
% 0.22/0.60  fof(f94,plain,(
% 0.22/0.60    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f93,f19])).
% 0.22/0.60  fof(f93,plain,(
% 0.22/0.60    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(subsumption_resolution,[],[f92,f20])).
% 0.22/0.60  fof(f92,plain,(
% 0.22/0.60    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(resolution,[],[f56,f21])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    ( ! [X6,X8,X7] : (~m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8)) | k2_mcart_1(sK3) = k7_mcart_1(X6,X7,X8,sK3) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.22/0.60    inference(backward_demodulation,[],[f49,f53])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    k2_mcart_1(sK3) = sK6(sK0,sK1,sK2,sK3)),
% 0.22/0.60    inference(superposition,[],[f27,f46])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X6,X8,X7] : (~m1_subset_1(sK3,k3_zfmisc_1(X6,X7,X8)) | sK6(sK0,sK1,sK2,sK3) = k7_mcart_1(X6,X7,X8,sK3) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.22/0.60    inference(superposition,[],[f37,f46])).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X6 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(equality_resolution,[],[f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f25,f32])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.60    inference(cnf_transformation,[],[f13])).
% 0.22/0.60  fof(f102,plain,(
% 0.22/0.60    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.60    inference(resolution,[],[f78,f21])).
% 0.22/0.60  fof(f78,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)) | k1_mcart_1(k1_mcart_1(sK3)) = k5_mcart_1(X0,X1,X2,sK3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(backward_demodulation,[],[f47,f72])).
% 0.22/0.60  fof(f72,plain,(
% 0.22/0.60    k1_mcart_1(k1_mcart_1(sK3)) = sK4(sK0,sK1,sK2,sK3)),
% 0.22/0.60    inference(superposition,[],[f26,f54])).
% 0.22/0.60  fof(f47,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)) | sK4(sK0,sK1,sK2,sK3) = k5_mcart_1(X0,X1,X2,sK3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(superposition,[],[f39,f46])).
% 0.22/0.60  fof(f39,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(equality_resolution,[],[f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f23,f32])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | k3_mcart_1(X4,X5,X6) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (30539)------------------------------
% 0.22/0.60  % (30539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (30539)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (30539)Memory used [KB]: 6396
% 0.22/0.60  % (30539)Time elapsed: 0.150 s
% 0.22/0.60  % (30539)------------------------------
% 0.22/0.60  % (30539)------------------------------
% 0.22/0.60  % (30533)Success in time 0.23 s
%------------------------------------------------------------------------------
