%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:56 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  138 (3642 expanded)
%              Number of leaves         :   25 ( 975 expanded)
%              Depth                    :   35
%              Number of atoms          :  377 (14401 expanded)
%              Number of equality atoms :  118 (2949 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1459,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1458,f172])).

fof(f172,plain,(
    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f125,f160])).

fof(f160,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f66,f139])).

fof(f139,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f135,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f135,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f126,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f126,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f119,f101])).

fof(f101,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f119,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f113,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f125,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f124,f56])).

fof(f124,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f123,f118])).

fof(f118,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f112,f111])).

fof(f111,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f112,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f56,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f123,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f117,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f117,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f108,f111])).

fof(f108,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f57,f59])).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f1458,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1457,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1457,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1456,f376])).

fof(f376,plain,(
    ! [X16] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X16) ),
    inference(resolution,[],[f299,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f299,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f273,f278])).

fof(f278,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f272,f61])).

fof(f272,plain,(
    ! [X4] : ~ r2_hidden(X4,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f270,f238])).

fof(f238,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_xboole_0(sK1,sK1))
      | r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f104,f143])).

fof(f143,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f66,f135])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f270,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,k5_xboole_0(sK1,sK1)) ) ),
    inference(superposition,[],[f103,f240])).

fof(f240,plain,(
    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f239,f139])).

fof(f239,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f232,f62])).

fof(f232,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f67,f143])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f273,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k5_xboole_0(sK1,sK1),X1)) ),
    inference(resolution,[],[f272,f107])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1456,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f1455,f62])).

fof(f1455,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1454,f691])).

fof(f691,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f678,f659])).

fof(f659,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f651,f445])).

fof(f445,plain,(
    ! [X16] : k1_xboole_0 = k3_xboole_0(X16,k1_xboole_0) ),
    inference(resolution,[],[f300,f61])).

fof(f300,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f274,f278])).

fof(f274,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(X3,k5_xboole_0(sK1,sK1))) ),
    inference(resolution,[],[f272,f106])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f651,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f67,f622])).

fof(f622,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f611,f60])).

fof(f611,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f66,f445])).

fof(f678,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f66,f674])).

fof(f674,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f664,f622])).

fof(f664,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f67,f659])).

fof(f1454,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f1452,f580])).

fof(f580,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f579,f178])).

fof(f178,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f164,f62])).

fof(f164,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f82,f139])).

fof(f82,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f579,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f565,f62])).

fof(f565,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(k5_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f82,f437])).

fof(f437,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f429,f293])).

fof(f293,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f240,f278])).

fof(f429,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f67,f395])).

fof(f395,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f308,f376])).

fof(f308,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f297,f62])).

fof(f297,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f265,f278])).

fof(f265,plain,(
    k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f67,f240])).

fof(f1452,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f68,f1421])).

fof(f1421,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1410,f1418])).

fof(f1418,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1417,f60])).

fof(f1417,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1409,f691])).

fof(f1409,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f161,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f161,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f68,f139])).

fof(f1410,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f161,f63])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12992)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (12986)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (12994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (12984)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (12977)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12978)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12994)Refutation not found, incomplete strategy% (12994)------------------------------
% 0.21/0.52  % (12994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12994)Memory used [KB]: 10746
% 0.21/0.52  % (12994)Time elapsed: 0.061 s
% 0.21/0.52  % (12994)------------------------------
% 0.21/0.52  % (12994)------------------------------
% 0.21/0.52  % (12982)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (12972)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12973)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (12997)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13009)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (12975)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (12987)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (12980)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (12993)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (12983)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (12988)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (12979)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (13004)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (13006)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (13002)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (12990)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (12995)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.66/0.60  % (12974)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.84/0.61  % (12999)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.63  % (12989)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.63  % (12981)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.63  % (12989)Refutation not found, incomplete strategy% (12989)------------------------------
% 1.84/0.63  % (12989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.64  % (12989)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.64  
% 1.84/0.64  % (12989)Memory used [KB]: 10618
% 1.84/0.64  % (12989)Time elapsed: 0.194 s
% 1.84/0.64  % (12989)------------------------------
% 1.84/0.64  % (12989)------------------------------
% 2.20/0.66  % (13020)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.69  % (12995)Refutation found. Thanks to Tanya!
% 2.20/0.69  % SZS status Theorem for theBenchmark
% 2.20/0.69  % SZS output start Proof for theBenchmark
% 2.20/0.69  fof(f1459,plain,(
% 2.20/0.69    $false),
% 2.20/0.69    inference(subsumption_resolution,[],[f1458,f172])).
% 2.20/0.69  fof(f172,plain,(
% 2.20/0.69    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.20/0.69    inference(backward_demodulation,[],[f125,f160])).
% 2.20/0.69  fof(f160,plain,(
% 2.20/0.69    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(superposition,[],[f66,f139])).
% 2.20/0.69  fof(f139,plain,(
% 2.20/0.69    sK1 = k3_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(superposition,[],[f135,f62])).
% 2.20/0.69  fof(f62,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f1])).
% 2.20/0.69  fof(f1,axiom,(
% 2.20/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.69  fof(f135,plain,(
% 2.20/0.69    sK1 = k3_xboole_0(sK1,sK0)),
% 2.20/0.69    inference(resolution,[],[f126,f73])).
% 2.20/0.69  fof(f73,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f32])).
% 2.20/0.69  fof(f32,plain,(
% 2.20/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.20/0.69    inference(ennf_transformation,[],[f8])).
% 2.20/0.69  fof(f8,axiom,(
% 2.20/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.20/0.69  fof(f126,plain,(
% 2.20/0.69    r1_tarski(sK1,sK0)),
% 2.20/0.69    inference(resolution,[],[f119,f101])).
% 2.20/0.69  fof(f101,plain,(
% 2.20/0.69    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(equality_resolution,[],[f76])).
% 2.20/0.69  fof(f76,plain,(
% 2.20/0.69    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.20/0.69    inference(cnf_transformation,[],[f45])).
% 2.20/0.69  fof(f45,plain,(
% 2.20/0.69    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 2.20/0.69  fof(f44,plain,(
% 2.20/0.69    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f43,plain,(
% 2.20/0.69    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.20/0.69    inference(rectify,[],[f42])).
% 2.20/0.69  fof(f42,plain,(
% 2.20/0.69    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.20/0.69    inference(nnf_transformation,[],[f19])).
% 2.20/0.69  fof(f19,axiom,(
% 2.20/0.69    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.20/0.69  fof(f119,plain,(
% 2.20/0.69    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(subsumption_resolution,[],[f113,f58])).
% 2.20/0.69  fof(f58,plain,(
% 2.20/0.69    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f25])).
% 2.20/0.69  fof(f25,axiom,(
% 2.20/0.69    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.20/0.69  fof(f113,plain,(
% 2.20/0.69    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(resolution,[],[f56,f69])).
% 2.20/0.69  fof(f69,plain,(
% 2.20/0.69    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f41])).
% 2.20/0.69  fof(f41,plain,(
% 2.20/0.69    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.20/0.69    inference(nnf_transformation,[],[f31])).
% 2.20/0.69  fof(f31,plain,(
% 2.20/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f21])).
% 2.20/0.69  fof(f21,axiom,(
% 2.20/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.20/0.69  fof(f56,plain,(
% 2.20/0.69    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(cnf_transformation,[],[f38])).
% 2.20/0.69  fof(f38,plain,(
% 2.20/0.69    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37])).
% 2.20/0.69  fof(f37,plain,(
% 2.20/0.69    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f29,plain,(
% 2.20/0.69    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f28])).
% 2.20/0.69  fof(f28,negated_conjecture,(
% 2.20/0.69    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.20/0.69    inference(negated_conjecture,[],[f27])).
% 2.20/0.69  fof(f27,conjecture,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.20/0.69  fof(f66,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f6])).
% 2.20/0.69  fof(f6,axiom,(
% 2.20/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.20/0.69  fof(f125,plain,(
% 2.20/0.69    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 2.20/0.69    inference(subsumption_resolution,[],[f124,f56])).
% 2.20/0.69  fof(f124,plain,(
% 2.20/0.69    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(subsumption_resolution,[],[f123,f118])).
% 2.20/0.69  fof(f118,plain,(
% 2.20/0.69    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(forward_demodulation,[],[f112,f111])).
% 2.20/0.69  fof(f111,plain,(
% 2.20/0.69    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(resolution,[],[f56,f75])).
% 2.20/0.69  fof(f75,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f34])).
% 2.20/0.69  fof(f34,plain,(
% 2.20/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f23])).
% 2.20/0.69  fof(f23,axiom,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.20/0.69  fof(f112,plain,(
% 2.20/0.69    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(resolution,[],[f56,f74])).
% 2.20/0.69  fof(f74,plain,(
% 2.20/0.69    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f33])).
% 2.20/0.69  fof(f33,plain,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f24])).
% 2.20/0.69  fof(f24,axiom,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.20/0.69  fof(f123,plain,(
% 2.20/0.69    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.69    inference(superposition,[],[f117,f83])).
% 2.20/0.69  fof(f83,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f36])).
% 2.20/0.69  fof(f36,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(flattening,[],[f35])).
% 2.20/0.69  fof(f35,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.20/0.69    inference(ennf_transformation,[],[f26])).
% 2.20/0.69  fof(f26,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.20/0.69  fof(f117,plain,(
% 2.20/0.69    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 2.20/0.69    inference(backward_demodulation,[],[f108,f111])).
% 2.20/0.69  fof(f108,plain,(
% 2.20/0.69    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f57,f59])).
% 2.20/0.69  fof(f59,plain,(
% 2.20/0.69    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.20/0.69    inference(cnf_transformation,[],[f22])).
% 2.20/0.69  fof(f22,axiom,(
% 2.20/0.69    ! [X0] : k2_subset_1(X0) = X0),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.20/0.69  fof(f57,plain,(
% 2.20/0.69    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.20/0.69    inference(cnf_transformation,[],[f38])).
% 2.20/0.69  fof(f1458,plain,(
% 2.20/0.69    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f1457,f60])).
% 2.20/0.69  fof(f60,plain,(
% 2.20/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.69    inference(cnf_transformation,[],[f10])).
% 2.20/0.69  fof(f10,axiom,(
% 2.20/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.20/0.69  fof(f1457,plain,(
% 2.20/0.69    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.20/0.69    inference(forward_demodulation,[],[f1456,f376])).
% 2.20/0.69  fof(f376,plain,(
% 2.20/0.69    ( ! [X16] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X16)) )),
% 2.20/0.69    inference(resolution,[],[f299,f61])).
% 2.20/0.69  fof(f61,plain,(
% 2.20/0.69    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.20/0.69    inference(cnf_transformation,[],[f40])).
% 2.20/0.69  fof(f40,plain,(
% 2.20/0.69    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f39])).
% 2.20/0.69  fof(f39,plain,(
% 2.20/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f30,plain,(
% 2.20/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.20/0.69    inference(ennf_transformation,[],[f5])).
% 2.20/0.69  fof(f5,axiom,(
% 2.20/0.69    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.20/0.69  fof(f299,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 2.20/0.69    inference(backward_demodulation,[],[f273,f278])).
% 2.20/0.69  fof(f278,plain,(
% 2.20/0.69    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(resolution,[],[f272,f61])).
% 2.20/0.69  fof(f272,plain,(
% 2.20/0.69    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f270,f238])).
% 2.20/0.69  fof(f238,plain,(
% 2.20/0.69    ( ! [X5] : (~r2_hidden(X5,k5_xboole_0(sK1,sK1)) | r2_hidden(X5,sK1)) )),
% 2.20/0.69    inference(superposition,[],[f104,f143])).
% 2.20/0.69  fof(f143,plain,(
% 2.20/0.69    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(superposition,[],[f66,f135])).
% 2.20/0.69  fof(f104,plain,(
% 2.20/0.69    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(equality_resolution,[],[f84])).
% 2.20/0.69  fof(f84,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.20/0.69    inference(cnf_transformation,[],[f50])).
% 2.20/0.69  fof(f50,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 2.20/0.69  fof(f49,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f48,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(rectify,[],[f47])).
% 2.20/0.69  fof(f47,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(flattening,[],[f46])).
% 2.20/0.69  fof(f46,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(nnf_transformation,[],[f4])).
% 2.20/0.69  fof(f4,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.20/0.69  fof(f270,plain,(
% 2.20/0.69    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r2_hidden(X4,k5_xboole_0(sK1,sK1))) )),
% 2.20/0.69    inference(superposition,[],[f103,f240])).
% 2.20/0.69  fof(f240,plain,(
% 2.20/0.69    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f239,f139])).
% 2.20/0.69  fof(f239,plain,(
% 2.20/0.69    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f232,f62])).
% 2.20/0.69  fof(f232,plain,(
% 2.20/0.69    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 2.20/0.69    inference(superposition,[],[f67,f143])).
% 2.20/0.69  fof(f67,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f9])).
% 2.20/0.69  fof(f9,axiom,(
% 2.20/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.20/0.69  fof(f103,plain,(
% 2.20/0.69    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(equality_resolution,[],[f85])).
% 2.20/0.69  fof(f85,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.20/0.69    inference(cnf_transformation,[],[f50])).
% 2.20/0.69  fof(f273,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k5_xboole_0(sK1,sK1),X1))) )),
% 2.20/0.69    inference(resolution,[],[f272,f107])).
% 2.20/0.69  fof(f107,plain,(
% 2.20/0.69    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(equality_resolution,[],[f90])).
% 2.20/0.69  fof(f90,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.20/0.69    inference(cnf_transformation,[],[f55])).
% 2.20/0.69  fof(f55,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).
% 2.20/0.69  fof(f54,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f53,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(rectify,[],[f52])).
% 2.20/0.69  fof(f52,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(flattening,[],[f51])).
% 2.20/0.69  fof(f51,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.20/0.69    inference(nnf_transformation,[],[f3])).
% 2.20/0.69  fof(f3,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.20/0.69  fof(f1456,plain,(
% 2.20/0.69    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f1455,f62])).
% 2.20/0.69  fof(f1455,plain,(
% 2.20/0.69    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0))),
% 2.20/0.69    inference(forward_demodulation,[],[f1454,f691])).
% 2.20/0.69  fof(f691,plain,(
% 2.20/0.69    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 2.20/0.69    inference(forward_demodulation,[],[f678,f659])).
% 2.20/0.69  fof(f659,plain,(
% 2.20/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.20/0.69    inference(forward_demodulation,[],[f651,f445])).
% 2.20/0.69  fof(f445,plain,(
% 2.20/0.69    ( ! [X16] : (k1_xboole_0 = k3_xboole_0(X16,k1_xboole_0)) )),
% 2.20/0.69    inference(resolution,[],[f300,f61])).
% 2.20/0.69  fof(f300,plain,(
% 2.20/0.69    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(X3,k1_xboole_0))) )),
% 2.20/0.69    inference(backward_demodulation,[],[f274,f278])).
% 2.20/0.69  fof(f274,plain,(
% 2.20/0.69    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(X3,k5_xboole_0(sK1,sK1)))) )),
% 2.20/0.69    inference(resolution,[],[f272,f106])).
% 2.20/0.69  fof(f106,plain,(
% 2.20/0.69    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(equality_resolution,[],[f91])).
% 2.20/0.69  fof(f91,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.20/0.69    inference(cnf_transformation,[],[f55])).
% 2.20/0.69  fof(f651,plain,(
% 2.20/0.69    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.20/0.69    inference(superposition,[],[f67,f622])).
% 2.20/0.69  fof(f622,plain,(
% 2.20/0.69    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.20/0.69    inference(forward_demodulation,[],[f611,f60])).
% 2.20/0.69  fof(f611,plain,(
% 2.20/0.69    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.20/0.69    inference(superposition,[],[f66,f445])).
% 2.20/0.69  fof(f678,plain,(
% 2.20/0.69    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 2.20/0.69    inference(superposition,[],[f66,f674])).
% 2.20/0.69  fof(f674,plain,(
% 2.20/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.20/0.69    inference(forward_demodulation,[],[f664,f622])).
% 2.20/0.69  fof(f664,plain,(
% 2.20/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 2.20/0.69    inference(superposition,[],[f67,f659])).
% 2.20/0.69  fof(f1454,plain,(
% 2.20/0.69    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 2.20/0.69    inference(forward_demodulation,[],[f1452,f580])).
% 2.20/0.69  fof(f580,plain,(
% 2.20/0.69    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 2.20/0.69    inference(forward_demodulation,[],[f579,f178])).
% 2.20/0.69  fof(f178,plain,(
% 2.20/0.69    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 2.20/0.69    inference(forward_demodulation,[],[f164,f62])).
% 2.20/0.69  fof(f164,plain,(
% 2.20/0.69    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1)) )),
% 2.20/0.69    inference(superposition,[],[f82,f139])).
% 2.20/0.69  fof(f82,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f7])).
% 2.20/0.69  fof(f7,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.20/0.69  fof(f579,plain,(
% 2.20/0.69    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 2.20/0.69    inference(forward_demodulation,[],[f565,f62])).
% 2.20/0.69  fof(f565,plain,(
% 2.20/0.69    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(k5_xboole_0(X1,sK1),sK1)) )),
% 2.20/0.69    inference(superposition,[],[f82,f437])).
% 2.20/0.69  fof(f437,plain,(
% 2.20/0.69    sK1 = k3_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(forward_demodulation,[],[f429,f293])).
% 2.20/0.69  fof(f293,plain,(
% 2.20/0.69    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 2.20/0.69    inference(backward_demodulation,[],[f240,f278])).
% 2.20/0.69  fof(f429,plain,(
% 2.20/0.69    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(superposition,[],[f67,f395])).
% 2.20/0.69  fof(f395,plain,(
% 2.20/0.69    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(backward_demodulation,[],[f308,f376])).
% 2.20/0.69  fof(f308,plain,(
% 2.20/0.69    k4_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1)),
% 2.20/0.69    inference(forward_demodulation,[],[f297,f62])).
% 2.20/0.69  fof(f297,plain,(
% 2.20/0.69    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0)),
% 2.20/0.69    inference(backward_demodulation,[],[f265,f278])).
% 2.20/0.69  fof(f265,plain,(
% 2.20/0.69    k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1)),
% 2.20/0.69    inference(superposition,[],[f67,f240])).
% 2.20/0.69  fof(f1452,plain,(
% 2.20/0.69    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.20/0.69    inference(superposition,[],[f68,f1421])).
% 2.20/0.69  fof(f1421,plain,(
% 2.20/0.69    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.20/0.69    inference(forward_demodulation,[],[f1410,f1418])).
% 2.20/0.69  fof(f1418,plain,(
% 2.20/0.69    sK0 = k2_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(forward_demodulation,[],[f1417,f60])).
% 2.20/0.69  fof(f1417,plain,(
% 2.20/0.69    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.20/0.69    inference(forward_demodulation,[],[f1409,f691])).
% 2.20/0.69  fof(f1409,plain,(
% 2.20/0.69    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(superposition,[],[f161,f81])).
% 2.20/0.69  fof(f81,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f11])).
% 2.20/0.69  fof(f11,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.20/0.69  fof(f161,plain,(
% 2.20/0.69    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(superposition,[],[f68,f139])).
% 2.20/0.69  fof(f1410,plain,(
% 2.20/0.69    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)),
% 2.20/0.69    inference(superposition,[],[f161,f63])).
% 2.20/0.69  fof(f63,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f2])).
% 2.20/0.69  fof(f2,axiom,(
% 2.20/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.20/0.69  fof(f68,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f12])).
% 2.20/0.69  fof(f12,axiom,(
% 2.20/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.20/0.69  % SZS output end Proof for theBenchmark
% 2.20/0.69  % (12995)------------------------------
% 2.20/0.69  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (12995)Termination reason: Refutation
% 2.20/0.69  
% 2.20/0.69  % (12995)Memory used [KB]: 2686
% 2.20/0.69  % (12995)Time elapsed: 0.265 s
% 2.20/0.69  % (12995)------------------------------
% 2.20/0.69  % (12995)------------------------------
% 2.20/0.69  % (12970)Success in time 0.323 s
%------------------------------------------------------------------------------
