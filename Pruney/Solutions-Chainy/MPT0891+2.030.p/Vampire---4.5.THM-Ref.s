%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 (1228 expanded)
%              Number of leaves         :   13 ( 430 expanded)
%              Depth                    :   23
%              Number of atoms          :  250 (7417 expanded)
%              Number of equality atoms :  194 (6203 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f124,f123])).

fof(f123,plain,(
    ! [X0] : r2_hidden(sK3,X0) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
      | r2_hidden(sK3,X0) ) ),
    inference(superposition,[],[f33,f107])).

fof(f107,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f106,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(superposition,[],[f93,f103])).

fof(f103,plain,
    ( sK3 = k2_mcart_1(sK3)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f102,f46])).

fof(f102,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(superposition,[],[f94,f99])).

fof(f99,plain,
    ( sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(sK3) ),
    inference(superposition,[],[f92,f77])).

fof(f77,plain,
    ( sK3 = k2_mcart_1(k1_mcart_1(sK3))
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(sK3) ),
    inference(superposition,[],[f75,f67])).

fof(f67,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k1_mcart_1(k1_mcart_1(sK3))
    | sK3 = k2_mcart_1(sK3) ),
    inference(backward_demodulation,[],[f60,f66])).

fof(f66,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f65,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f14,plain,(
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

fof(f65,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f60,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k2_mcart_1(sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f59,f29])).

fof(f29,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f58,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f55,f27])).

fof(f55,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f44,f28])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f74,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f73,f26])).

fof(f73,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f71,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,
    ( ~ r1_tarski(k1_tarski(k2_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(k2_mcart_1(k1_mcart_1(sK3))) ),
    inference(superposition,[],[f52,f88])).

fof(f88,plain,(
    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f87,f66])).

fof(f87,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f86,f75])).

fof(f86,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3)) ),
    inference(forward_demodulation,[],[f85,f59])).

fof(f85,plain,(
    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f84,f25])).

fof(f84,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f83,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f81,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X0,X1,X2)))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f40,f50])).

fof(f50,plain,(
    ! [X6,X4,X5] : k1_tarski(k3_mcart_1(X4,X5,X6)) = k3_zfmisc_1(k1_tarski(X4),k1_tarski(X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f48,f32])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X6,X4,X5] : k1_tarski(k3_mcart_1(X4,X5,X6)) = k3_zfmisc_1(k1_tarski(X4),k2_tarski(X5,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f45,f32])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f94,plain,
    ( ~ r1_tarski(k1_tarski(k1_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(k1_mcart_1(k1_mcart_1(sK3))) ),
    inference(superposition,[],[f54,f88])).

fof(f54,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8)))
      | k1_xboole_0 = k1_tarski(X6) ) ),
    inference(superposition,[],[f38,f50])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,
    ( ~ r1_tarski(k1_tarski(k2_mcart_1(sK3)),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(k2_mcart_1(sK3)) ),
    inference(superposition,[],[f53,f88])).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5)))
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(superposition,[],[f39,f50])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f124,plain,(
    ! [X1] : ~ r2_hidden(sK3,X1) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f115,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,k1_xboole_0) != X1
      | ~ r2_hidden(sK3,X1) ) ),
    inference(superposition,[],[f37,f107])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
     => ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:42:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (20052)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (20044)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (20044)Refutation not found, incomplete strategy% (20044)------------------------------
% 0.22/0.51  % (20044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20044)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20044)Memory used [KB]: 10746
% 0.22/0.51  % (20044)Time elapsed: 0.096 s
% 0.22/0.51  % (20044)------------------------------
% 0.22/0.51  % (20044)------------------------------
% 0.22/0.52  % (20043)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (20060)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (20048)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (20050)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (20041)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (20051)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20040)Refutation not found, incomplete strategy% (20040)------------------------------
% 0.22/0.53  % (20040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20040)Memory used [KB]: 6140
% 0.22/0.53  % (20040)Time elapsed: 0.104 s
% 0.22/0.53  % (20040)------------------------------
% 0.22/0.53  % (20040)------------------------------
% 0.22/0.53  % (20051)Refutation not found, incomplete strategy% (20051)------------------------------
% 0.22/0.53  % (20051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (20055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (20045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (20056)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (20059)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (20042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (20043)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f124,f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f114,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | r2_hidden(sK3,X0)) )),
% 0.22/0.54    inference(superposition,[],[f33,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    k1_xboole_0 = k1_tarski(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f106,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK3)),
% 0.22/0.54    inference(superposition,[],[f93,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    sK3 = k2_mcart_1(sK3) | k1_xboole_0 = k1_tarski(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f102,f46])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK3) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f94,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    sK3 = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = k1_tarski(sK3) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f46])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK3),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f92,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    sK3 = k2_mcart_1(k1_mcart_1(sK3)) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f75,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k1_mcart_1(k1_mcart_1(sK3)) | sK3 = k2_mcart_1(sK3)),
% 0.22/0.54    inference(backward_demodulation,[],[f60,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.54    inference(subsumption_resolution,[],[f65,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f64,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f62,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    k1_xboole_0 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f42,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k2_mcart_1(sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.54    inference(superposition,[],[f59,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f58,f25])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f57,f26])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f55,f27])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f44,f28])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.54    inference(subsumption_resolution,[],[f74,f25])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f73,f26])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f71,f27])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f43,f28])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(k2_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(k2_mcart_1(k1_mcart_1(sK3)))),
% 0.22/0.54    inference(superposition,[],[f52,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))),
% 0.22/0.54    inference(forward_demodulation,[],[f87,f66])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))),
% 0.22/0.54    inference(forward_demodulation,[],[f86,f75])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))),
% 0.22/0.54    inference(forward_demodulation,[],[f85,f59])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.22/0.54    inference(subsumption_resolution,[],[f84,f25])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f83,f26])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f27])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f41,f28])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(k3_mcart_1(X0,X1,X2))) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.22/0.54    inference(superposition,[],[f40,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (k1_tarski(k3_mcart_1(X4,X5,X6)) = k3_zfmisc_1(k1_tarski(X4),k1_tarski(X5),k1_tarski(X6))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f48,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X6,X4,X5] : (k1_tarski(k3_mcart_1(X4,X5,X6)) = k3_zfmisc_1(k1_tarski(X4),k2_tarski(X5,X5),k1_tarski(X6))) )),
% 0.22/0.54    inference(superposition,[],[f45,f32])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(k1_mcart_1(k1_mcart_1(sK3))),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(k1_mcart_1(k1_mcart_1(sK3)))),
% 0.22/0.54    inference(superposition,[],[f54,f88])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X6,X8,X7] : (~r1_tarski(k1_tarski(X6),k1_tarski(k3_mcart_1(X6,X7,X8))) | k1_xboole_0 = k1_tarski(X6)) )),
% 0.22/0.54    inference(superposition,[],[f38,f50])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(k2_mcart_1(sK3)),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(k2_mcart_1(sK3))),
% 0.22/0.54    inference(superposition,[],[f53,f88])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~r1_tarski(k1_tarski(X5),k1_tarski(k3_mcart_1(X3,X4,X5))) | k1_xboole_0 = k1_tarski(X5)) )),
% 0.22/0.54    inference(superposition,[],[f39,f50])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(sK3,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f115,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) != X1 | ~r2_hidden(sK3,X1)) )),
% 0.22/0.54    inference(superposition,[],[f37,f107])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 => ~r2_hidden(X1,X0))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (20043)------------------------------
% 0.22/0.54  % (20043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20043)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (20043)Memory used [KB]: 6396
% 0.22/0.54  % (20043)Time elapsed: 0.119 s
% 0.22/0.54  % (20043)------------------------------
% 0.22/0.54  % (20043)------------------------------
% 0.22/0.54  % (20036)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20053)Refutation not found, incomplete strategy% (20053)------------------------------
% 0.22/0.54  % (20053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20053)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20053)Memory used [KB]: 10618
% 0.22/0.54  % (20053)Time elapsed: 0.121 s
% 0.22/0.54  % (20053)------------------------------
% 0.22/0.54  % (20053)------------------------------
% 0.22/0.54  % (20035)Success in time 0.165 s
%------------------------------------------------------------------------------
