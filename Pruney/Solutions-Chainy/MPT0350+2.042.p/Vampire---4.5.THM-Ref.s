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
% DateTime   : Thu Dec  3 12:43:55 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  112 (1017 expanded)
%              Number of leaves         :   23 ( 276 expanded)
%              Depth                    :   20
%              Number of atoms          :  280 (3463 expanded)
%              Number of equality atoms :   92 ( 790 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2452,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2449,f145])).

fof(f145,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f112,f140])).

fof(f140,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f72,f128])).

fof(f128,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f127,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f127,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f119,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f119,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f113,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f113,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f108,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f108,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f57,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f112,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f104,f107])).

fof(f107,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f58,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f58,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f2449,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f869,f2448])).

fof(f2448,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2445,f2419])).

fof(f2419,plain,(
    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2418,f2411])).

fof(f2411,plain,(
    sK0 = k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f141,f2405])).

fof(f2405,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2404,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2404,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2395,f208])).

fof(f208,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f206,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f206,plain,(
    ! [X4] : ~ r2_hidden(X4,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f202,f172])).

fof(f172,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(sK1,sK1))
      | r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f103,f133])).

fof(f133,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f72,f127])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
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

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f202,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f102,f136])).

fof(f136,plain,(
    k4_xboole_0(sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f132,f133])).

fof(f132,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f71,f127])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2395,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f149,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f149,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f138,f148])).

fof(f148,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f137,f141])).

fof(f137,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f134,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f134,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f74,f127])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f138,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f135,f68])).

fof(f135,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f75,f127])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f141,plain,(
    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f74,f128])).

fof(f2418,plain,(
    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2417,f2405])).

fof(f2417,plain,(
    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2400,f67])).

fof(f2400,plain,(
    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[],[f75,f149])).

fof(f2445,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f75,f2412])).

fof(f2412,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2396,f2405])).

fof(f2396,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f149,f68])).

fof(f869,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f105,f756])).

fof(f756,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f752,f59])).

fof(f752,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f747,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f747,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f738,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f738,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f66,f140])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (9534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (9551)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (9550)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (9527)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (9542)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (9531)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (9537)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (9532)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (9535)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (9549)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (9541)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (9549)Refutation not found, incomplete strategy% (9549)------------------------------
% 0.20/0.53  % (9549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9549)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (9549)Memory used [KB]: 10746
% 0.20/0.53  % (9549)Time elapsed: 0.078 s
% 0.20/0.53  % (9549)------------------------------
% 0.20/0.53  % (9549)------------------------------
% 0.20/0.53  % (9555)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (9533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (9552)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (9529)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (9530)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (9556)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (9528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (9538)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (9537)Refutation not found, incomplete strategy% (9537)------------------------------
% 0.20/0.54  % (9537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9537)Memory used [KB]: 10618
% 0.20/0.54  % (9537)Time elapsed: 0.125 s
% 0.20/0.54  % (9537)------------------------------
% 0.20/0.54  % (9537)------------------------------
% 0.20/0.54  % (9538)Refutation not found, incomplete strategy% (9538)------------------------------
% 0.20/0.54  % (9538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9538)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9538)Memory used [KB]: 10618
% 0.20/0.54  % (9538)Time elapsed: 0.125 s
% 0.20/0.54  % (9538)------------------------------
% 0.20/0.54  % (9538)------------------------------
% 0.20/0.54  % (9553)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (9543)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (9545)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (9554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (9544)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (9547)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (9548)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (9536)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (9546)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (9540)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (9539)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (9544)Refutation not found, incomplete strategy% (9544)------------------------------
% 0.20/0.55  % (9544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (9544)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (9544)Memory used [KB]: 10618
% 0.20/0.55  % (9544)Time elapsed: 0.147 s
% 0.20/0.55  % (9544)------------------------------
% 0.20/0.55  % (9544)------------------------------
% 2.12/0.68  % (9558)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.69  % (9557)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.70  % (9559)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.70  % (9560)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.70/0.72  % (9550)Refutation found. Thanks to Tanya!
% 2.70/0.72  % SZS status Theorem for theBenchmark
% 2.70/0.74  % SZS output start Proof for theBenchmark
% 2.70/0.74  fof(f2452,plain,(
% 2.70/0.74    $false),
% 2.70/0.74    inference(subsumption_resolution,[],[f2449,f145])).
% 2.70/0.74  fof(f145,plain,(
% 2.70/0.74    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(backward_demodulation,[],[f112,f140])).
% 2.70/0.74  fof(f140,plain,(
% 2.70/0.74    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(superposition,[],[f72,f128])).
% 2.70/0.74  fof(f128,plain,(
% 2.70/0.74    sK1 = k3_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(superposition,[],[f127,f67])).
% 2.70/0.74  fof(f67,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f1])).
% 2.70/0.74  fof(f1,axiom,(
% 2.70/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.70/0.74  fof(f127,plain,(
% 2.70/0.74    sK1 = k3_xboole_0(sK1,sK0)),
% 2.70/0.74    inference(resolution,[],[f119,f80])).
% 2.70/0.74  fof(f80,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f35])).
% 2.70/0.74  fof(f35,plain,(
% 2.70/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.70/0.74    inference(ennf_transformation,[],[f8])).
% 2.70/0.74  fof(f8,axiom,(
% 2.70/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.70/0.74  fof(f119,plain,(
% 2.70/0.74    r1_tarski(sK1,sK0)),
% 2.70/0.74    inference(resolution,[],[f113,f100])).
% 2.70/0.74  fof(f100,plain,(
% 2.70/0.74    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.70/0.74    inference(equality_resolution,[],[f82])).
% 2.70/0.74  fof(f82,plain,(
% 2.70/0.74    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.70/0.74    inference(cnf_transformation,[],[f51])).
% 2.70/0.74  fof(f51,plain,(
% 2.70/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 2.70/0.74  fof(f50,plain,(
% 2.70/0.74    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.70/0.74    introduced(choice_axiom,[])).
% 2.70/0.74  fof(f49,plain,(
% 2.70/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.74    inference(rectify,[],[f48])).
% 2.70/0.74  fof(f48,plain,(
% 2.70/0.74    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.74    inference(nnf_transformation,[],[f22])).
% 2.70/0.74  fof(f22,axiom,(
% 2.70/0.74    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.70/0.74  fof(f113,plain,(
% 2.70/0.74    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(subsumption_resolution,[],[f108,f59])).
% 2.70/0.74  fof(f59,plain,(
% 2.70/0.74    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f27])).
% 2.70/0.74  fof(f27,axiom,(
% 2.70/0.74    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.70/0.74  fof(f108,plain,(
% 2.70/0.74    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(resolution,[],[f57,f76])).
% 2.70/0.74  fof(f76,plain,(
% 2.70/0.74    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f47])).
% 2.70/0.74  fof(f47,plain,(
% 2.70/0.74    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.70/0.74    inference(nnf_transformation,[],[f34])).
% 2.70/0.74  fof(f34,plain,(
% 2.70/0.74    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.70/0.74    inference(ennf_transformation,[],[f24])).
% 2.70/0.74  fof(f24,axiom,(
% 2.70/0.74    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.70/0.74  fof(f57,plain,(
% 2.70/0.74    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(cnf_transformation,[],[f40])).
% 2.70/0.74  fof(f40,plain,(
% 2.70/0.74    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f39])).
% 2.70/0.74  fof(f39,plain,(
% 2.70/0.74    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.70/0.74    introduced(choice_axiom,[])).
% 2.70/0.74  fof(f32,plain,(
% 2.70/0.74    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.74    inference(ennf_transformation,[],[f30])).
% 2.70/0.74  fof(f30,negated_conjecture,(
% 2.70/0.74    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.70/0.74    inference(negated_conjecture,[],[f29])).
% 2.70/0.74  fof(f29,conjecture,(
% 2.70/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 2.70/0.74  fof(f72,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f7])).
% 2.70/0.74  fof(f7,axiom,(
% 2.70/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.70/0.74  fof(f112,plain,(
% 2.70/0.74    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(backward_demodulation,[],[f104,f107])).
% 2.70/0.74  fof(f107,plain,(
% 2.70/0.74    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(resolution,[],[f57,f81])).
% 2.70/0.74  fof(f81,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f36])).
% 2.70/0.74  fof(f36,plain,(
% 2.70/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.74    inference(ennf_transformation,[],[f26])).
% 2.70/0.74  fof(f26,axiom,(
% 2.70/0.74    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.70/0.74  fof(f104,plain,(
% 2.70/0.74    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.70/0.74    inference(forward_demodulation,[],[f58,f60])).
% 2.70/0.74  fof(f60,plain,(
% 2.70/0.74    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.70/0.74    inference(cnf_transformation,[],[f25])).
% 2.70/0.74  fof(f25,axiom,(
% 2.70/0.74    ! [X0] : k2_subset_1(X0) = X0),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.70/0.74  fof(f58,plain,(
% 2.70/0.74    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.70/0.74    inference(cnf_transformation,[],[f40])).
% 2.70/0.74  fof(f2449,plain,(
% 2.70/0.74    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(backward_demodulation,[],[f869,f2448])).
% 2.70/0.74  fof(f2448,plain,(
% 2.70/0.74    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(forward_demodulation,[],[f2445,f2419])).
% 2.70/0.74  fof(f2419,plain,(
% 2.70/0.74    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.70/0.74    inference(forward_demodulation,[],[f2418,f2411])).
% 2.70/0.74  fof(f2411,plain,(
% 2.70/0.74    sK0 = k2_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 2.70/0.74    inference(backward_demodulation,[],[f141,f2405])).
% 2.70/0.74  fof(f2405,plain,(
% 2.70/0.74    sK0 = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(forward_demodulation,[],[f2404,f61])).
% 2.70/0.74  fof(f61,plain,(
% 2.70/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.70/0.74    inference(cnf_transformation,[],[f12])).
% 2.70/0.74  fof(f12,axiom,(
% 2.70/0.74    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.70/0.74  fof(f2404,plain,(
% 2.70/0.74    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.70/0.74    inference(forward_demodulation,[],[f2395,f208])).
% 2.70/0.74  fof(f208,plain,(
% 2.70/0.74    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 2.70/0.74    inference(resolution,[],[f206,f64])).
% 2.70/0.74  fof(f64,plain,(
% 2.70/0.74    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.70/0.74    inference(cnf_transformation,[],[f46])).
% 2.70/0.74  fof(f46,plain,(
% 2.70/0.74    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.70/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f45])).
% 2.70/0.74  fof(f45,plain,(
% 2.70/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.70/0.74    introduced(choice_axiom,[])).
% 2.70/0.74  fof(f33,plain,(
% 2.70/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.70/0.74    inference(ennf_transformation,[],[f6])).
% 2.70/0.74  fof(f6,axiom,(
% 2.70/0.74    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.70/0.74  fof(f206,plain,(
% 2.70/0.74    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 2.70/0.74    inference(subsumption_resolution,[],[f202,f172])).
% 2.70/0.74  fof(f172,plain,(
% 2.70/0.74    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK1,sK1)) | r2_hidden(X5,sK1)) )),
% 2.70/0.74    inference(superposition,[],[f103,f133])).
% 2.70/0.74  fof(f133,plain,(
% 2.70/0.74    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 2.70/0.74    inference(superposition,[],[f72,f127])).
% 2.70/0.74  fof(f103,plain,(
% 2.70/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(equality_resolution,[],[f89])).
% 2.70/0.74  fof(f89,plain,(
% 2.70/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.74    inference(cnf_transformation,[],[f56])).
% 2.70/0.74  fof(f56,plain,(
% 2.70/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).
% 2.70/0.74  fof(f55,plain,(
% 2.70/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.70/0.74    introduced(choice_axiom,[])).
% 2.70/0.74  fof(f54,plain,(
% 2.70/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.74    inference(rectify,[],[f53])).
% 2.70/0.74  fof(f53,plain,(
% 2.70/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.74    inference(flattening,[],[f52])).
% 2.70/0.74  fof(f52,plain,(
% 2.70/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.74    inference(nnf_transformation,[],[f4])).
% 2.70/0.74  fof(f4,axiom,(
% 2.70/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.70/0.74  fof(f202,plain,(
% 2.70/0.74    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X4,sK1)) )),
% 2.70/0.74    inference(superposition,[],[f102,f136])).
% 2.70/0.74  fof(f136,plain,(
% 2.70/0.74    k4_xboole_0(sK1,sK1) = k5_xboole_0(sK1,sK1)),
% 2.70/0.74    inference(backward_demodulation,[],[f132,f133])).
% 2.70/0.74  fof(f132,plain,(
% 2.70/0.74    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1)),
% 2.70/0.74    inference(superposition,[],[f71,f127])).
% 2.70/0.74  fof(f71,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f10])).
% 2.70/0.74  fof(f10,axiom,(
% 2.70/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.70/0.74  fof(f102,plain,(
% 2.70/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(equality_resolution,[],[f90])).
% 2.70/0.74  fof(f90,plain,(
% 2.70/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.74    inference(cnf_transformation,[],[f56])).
% 2.70/0.74  fof(f2395,plain,(
% 2.70/0.74    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(superposition,[],[f149,f87])).
% 2.70/0.74  fof(f87,plain,(
% 2.70/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f13])).
% 2.70/0.74  fof(f13,axiom,(
% 2.70/0.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.70/0.74  fof(f149,plain,(
% 2.70/0.74    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(backward_demodulation,[],[f138,f148])).
% 2.70/0.74  fof(f148,plain,(
% 2.70/0.74    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(backward_demodulation,[],[f137,f141])).
% 2.70/0.74  fof(f137,plain,(
% 2.70/0.74    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 2.70/0.74    inference(forward_demodulation,[],[f134,f68])).
% 2.70/0.74  fof(f68,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f2])).
% 2.70/0.74  fof(f2,axiom,(
% 2.70/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.70/0.74  fof(f134,plain,(
% 2.70/0.74    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 2.70/0.74    inference(superposition,[],[f74,f127])).
% 2.70/0.74  fof(f74,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f14])).
% 2.70/0.74  fof(f14,axiom,(
% 2.70/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.70/0.74  fof(f138,plain,(
% 2.70/0.74    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 2.70/0.74    inference(forward_demodulation,[],[f135,f68])).
% 2.70/0.74  fof(f135,plain,(
% 2.70/0.74    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 2.70/0.74    inference(superposition,[],[f75,f127])).
% 2.70/0.74  fof(f75,plain,(
% 2.70/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f15])).
% 2.70/0.74  fof(f15,axiom,(
% 2.70/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.70/0.74  fof(f141,plain,(
% 2.70/0.74    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(superposition,[],[f74,f128])).
% 2.70/0.74  fof(f2418,plain,(
% 2.70/0.74    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.70/0.74    inference(forward_demodulation,[],[f2417,f2405])).
% 2.70/0.74  fof(f2417,plain,(
% 2.70/0.74    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.70/0.74    inference(forward_demodulation,[],[f2400,f67])).
% 2.70/0.74  fof(f2400,plain,(
% 2.70/0.74    k2_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 2.70/0.74    inference(superposition,[],[f75,f149])).
% 2.70/0.74  fof(f2445,plain,(
% 2.70/0.74    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.70/0.74    inference(superposition,[],[f75,f2412])).
% 2.70/0.74  fof(f2412,plain,(
% 2.70/0.74    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(forward_demodulation,[],[f2396,f2405])).
% 2.70/0.74  fof(f2396,plain,(
% 2.70/0.74    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)),
% 2.70/0.74    inference(superposition,[],[f149,f68])).
% 2.70/0.74  fof(f869,plain,(
% 2.70/0.74    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.70/0.74    inference(resolution,[],[f105,f756])).
% 2.70/0.74  fof(f756,plain,(
% 2.70/0.74    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(subsumption_resolution,[],[f752,f59])).
% 2.70/0.74  fof(f752,plain,(
% 2.70/0.74    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(resolution,[],[f747,f77])).
% 2.70/0.74  fof(f77,plain,(
% 2.70/0.74    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f47])).
% 2.70/0.74  fof(f747,plain,(
% 2.70/0.74    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.70/0.74    inference(resolution,[],[f738,f99])).
% 2.70/0.74  fof(f99,plain,(
% 2.70/0.74    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.70/0.74    inference(equality_resolution,[],[f83])).
% 2.70/0.74  fof(f83,plain,(
% 2.70/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.70/0.74    inference(cnf_transformation,[],[f51])).
% 2.70/0.74  fof(f738,plain,(
% 2.70/0.74    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 2.70/0.74    inference(superposition,[],[f66,f140])).
% 2.70/0.74  fof(f66,plain,(
% 2.70/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.70/0.74    inference(cnf_transformation,[],[f9])).
% 2.70/0.74  fof(f9,axiom,(
% 2.70/0.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.70/0.74  fof(f105,plain,(
% 2.70/0.74    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 2.70/0.74    inference(resolution,[],[f57,f88])).
% 2.70/0.74  fof(f88,plain,(
% 2.70/0.74    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.70/0.74    inference(cnf_transformation,[],[f38])).
% 2.70/0.74  fof(f38,plain,(
% 2.70/0.74    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.74    inference(flattening,[],[f37])).
% 2.70/0.74  fof(f37,plain,(
% 2.70/0.74    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.70/0.74    inference(ennf_transformation,[],[f28])).
% 2.70/0.74  fof(f28,axiom,(
% 2.70/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.70/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.70/0.74  % SZS output end Proof for theBenchmark
% 2.70/0.74  % (9550)------------------------------
% 2.70/0.74  % (9550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.74  % (9550)Termination reason: Refutation
% 2.70/0.74  
% 2.70/0.74  % (9550)Memory used [KB]: 2942
% 2.70/0.74  % (9550)Time elapsed: 0.299 s
% 2.70/0.74  % (9550)------------------------------
% 2.70/0.74  % (9550)------------------------------
% 2.70/0.74  % (9526)Success in time 0.386 s
%------------------------------------------------------------------------------
