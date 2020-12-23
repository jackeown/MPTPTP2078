%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 555 expanded)
%              Number of leaves         :    9 ( 166 expanded)
%              Depth                    :   26
%              Number of atoms          :  275 (4365 expanded)
%              Number of equality atoms :  169 (2622 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X6
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X6
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f102,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f100,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f100,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f99,f18])).

fof(f18,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,
    ( ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f98,f97])).

fof(f97,plain,(
    ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(subsumption_resolution,[],[f91,f96])).

fof(f96,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(subsumption_resolution,[],[f95,f20])).

fof(f95,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f21])).

fof(f94,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f93,f22])).

fof(f93,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f18])).

fof(f92,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f84])).

fof(f84,plain,(
    k2_mcart_1(k1_mcart_1(sK4)) = sK6(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f33,f68])).

fof(f68,plain,(
    k1_mcart_1(sK4) = k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)) ),
    inference(superposition,[],[f32,f64])).

fof(f64,plain,(
    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f62,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f58,f22])).

fof(f58,plain,
    ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f35,f18])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK7(X0,X1,X2,X3),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f16,f15,f14])).

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
                ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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

fof(f32,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(backward_demodulation,[],[f89,f85])).

fof(f85,plain,(
    k1_mcart_1(k1_mcart_1(sK4)) = sK5(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f32,f68])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f88,f57])).

fof(f57,plain,(
    sK3 != k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f23,f56])).

fof(f56,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f55,f20])).

fof(f55,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f54,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f50,f22])).

fof(f50,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f25,f18])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f23,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(forward_demodulation,[],[f86,f84])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(backward_demodulation,[],[f82,f84])).

fof(f82,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f71,f81])).

fof(f81,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f80,f20])).

fof(f80,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f79,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f77,f18])).

fof(f77,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f29,f67])).

fof(f67,plain,(
    k2_mcart_1(sK4) = sK7(sK0,sK1,sK2,sK4) ),
    inference(superposition,[],[f33,f64])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(backward_demodulation,[],[f69,f67])).

fof(f69,plain,
    ( sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( sK4 != sK4
    | sK3 = sK6(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(superposition,[],[f34,f64])).

fof(f34,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X6
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f19,f31])).

fof(f19,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X6
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f85])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (4104)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (4099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f102,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f101,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f100,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    k1_xboole_0 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f99,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f95,f20])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f94,f21])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f93,f22])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f18])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(superposition,[],[f28,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    k2_mcart_1(k1_mcart_1(sK4)) = sK6(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(superposition,[],[f33,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    k1_mcart_1(sK4) = k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4))),
% 0.21/0.54    inference(superposition,[],[f32,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f63,f20])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f62,f21])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f58,f22])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4)),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(resolution,[],[f35,f18])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3)),sK7(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f16,f15,f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f89,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    k1_mcart_1(k1_mcart_1(sK4)) = sK5(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(superposition,[],[f32,f68])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f88,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    sK3 != k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(superposition,[],[f23,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f55,f20])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f54,f21])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f50,f22])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(resolution,[],[f25,f18])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    sK3 = k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f86,f84])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f82,f84])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f71,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f80,f20])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f79,f21])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f22])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(sK4),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(subsumption_resolution,[],[f77,f18])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(superposition,[],[f29,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    k2_mcart_1(sK4) = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(superposition,[],[f33,f64])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~m1_subset_1(k2_mcart_1(sK4),sK2) | sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f69,f67])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    sK4 != sK4 | sK3 = sK6(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.54    inference(superposition,[],[f34,f64])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X6 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f31])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (sK3 = X6 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.54    inference(superposition,[],[f27,f85])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (4104)------------------------------
% 0.21/0.54  % (4104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4104)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (4104)Memory used [KB]: 6396
% 0.21/0.54  % (4104)Time elapsed: 0.113 s
% 0.21/0.54  % (4104)------------------------------
% 0.21/0.54  % (4104)------------------------------
% 0.21/0.54  % (4098)Success in time 0.181 s
%------------------------------------------------------------------------------
