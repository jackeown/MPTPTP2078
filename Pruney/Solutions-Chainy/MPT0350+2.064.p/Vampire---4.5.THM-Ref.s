%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 430 expanded)
%              Number of leaves         :   19 ( 121 expanded)
%              Depth                    :   31
%              Number of atoms          :  199 (1175 expanded)
%              Number of equality atoms :   90 ( 335 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(subsumption_resolution,[],[f493,f109])).

fof(f109,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f80,f103])).

fof(f103,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f50,f90])).

fof(f90,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f89,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f89,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f81,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f81,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f76,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f80,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f72,f75])).

fof(f75,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f40,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f493,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f267,f492])).

fof(f492,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f491,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f491,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f490,f117])).

fof(f117,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f115,f56])).

fof(f115,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f45,f98])).

fof(f98,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f94,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f94,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f50,f89])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f490,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f489,f46])).

fof(f489,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f488,f43])).

fof(f488,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(backward_demodulation,[],[f227,f487])).

fof(f487,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f486,f114])).

fof(f114,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f107,f46])).

fof(f107,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f64,f90])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f486,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f479,f46])).

fof(f479,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(k5_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f64,f463])).

fof(f463,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f461,f56])).

fof(f461,plain,(
    r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f45,f450])).

fof(f450,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f445,f44])).

fof(f445,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f50,f427])).

fof(f427,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f389,f245])).

fof(f245,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f243,f56])).

fof(f243,plain,(
    r1_tarski(k1_xboole_0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f45,f238])).

fof(f238,plain,(
    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f234,f43])).

fof(f234,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f50,f171])).

fof(f171,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f169,f56])).

fof(f169,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f45,f103])).

fof(f389,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f315,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f315,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f314,f44])).

fof(f314,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f308,f46])).

fof(f308,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k5_xboole_0(X1,sK0),k1_xboole_0) ),
    inference(superposition,[],[f64,f292])).

fof(f292,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f286,f43])).

fof(f286,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f100,f89])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f96,f46])).

fof(f96,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f64,f89])).

fof(f227,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f51,f206])).

fof(f206,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f195,f203])).

fof(f203,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f202,f44])).

fof(f202,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f194,f43])).

fof(f194,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f104,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f104,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f51,f90])).

fof(f195,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f104,f47])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f267,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f73,f176])).

fof(f176,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f173,f41])).

fof(f173,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f170,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f169,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f39,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15172)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (15171)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (15174)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (15173)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (15194)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (15187)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (15176)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (15192)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (15182)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15181)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15184)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (15183)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (15170)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (15195)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (15188)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (15192)Refutation not found, incomplete strategy% (15192)------------------------------
% 0.22/0.54  % (15192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15192)Memory used [KB]: 10746
% 0.22/0.54  % (15192)Time elapsed: 0.092 s
% 0.22/0.54  % (15192)------------------------------
% 0.22/0.54  % (15192)------------------------------
% 0.22/0.54  % (15189)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (15175)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15178)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (15190)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (15193)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (15187)Refutation not found, incomplete strategy% (15187)------------------------------
% 0.22/0.54  % (15187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15187)Memory used [KB]: 10618
% 0.22/0.54  % (15187)Time elapsed: 0.128 s
% 0.22/0.54  % (15187)------------------------------
% 0.22/0.54  % (15187)------------------------------
% 0.22/0.54  % (15198)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (15185)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (15185)Refutation not found, incomplete strategy% (15185)------------------------------
% 0.22/0.55  % (15185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15196)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (15185)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15185)Memory used [KB]: 6140
% 0.22/0.55  % (15185)Time elapsed: 0.004 s
% 0.22/0.55  % (15185)------------------------------
% 0.22/0.55  % (15185)------------------------------
% 0.22/0.55  % (15197)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (15179)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (15186)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (15181)Refutation not found, incomplete strategy% (15181)------------------------------
% 0.22/0.55  % (15181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15181)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15181)Memory used [KB]: 10618
% 0.22/0.55  % (15181)Time elapsed: 0.144 s
% 0.22/0.55  % (15181)------------------------------
% 0.22/0.55  % (15181)------------------------------
% 0.22/0.55  % (15199)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (15180)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (15191)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (15177)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (15180)Refutation not found, incomplete strategy% (15180)------------------------------
% 0.22/0.56  % (15180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15180)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15180)Memory used [KB]: 10618
% 0.22/0.56  % (15180)Time elapsed: 0.143 s
% 0.22/0.56  % (15180)------------------------------
% 0.22/0.56  % (15180)------------------------------
% 0.22/0.58  % (15193)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f497,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f493,f109])).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(backward_demodulation,[],[f80,f103])).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(superposition,[],[f50,f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(superposition,[],[f89,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.58    inference(resolution,[],[f84,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    r1_tarski(sK1,sK0)),
% 0.22/0.58    inference(resolution,[],[f81,f71])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(equality_resolution,[],[f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.58    inference(rectify,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,axiom,(
% 0.22/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(subsumption_resolution,[],[f76,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,axiom,(
% 0.22/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(resolution,[],[f39,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(nnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.22/0.58    inference(negated_conjecture,[],[f24])).
% 0.22/0.58  fof(f24,conjecture,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(backward_demodulation,[],[f72,f75])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(resolution,[],[f39,f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.58    inference(forward_demodulation,[],[f40,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f493,plain,(
% 0.22/0.58    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(backward_demodulation,[],[f267,f492])).
% 0.22/0.58  fof(f492,plain,(
% 0.22/0.58    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(forward_demodulation,[],[f491,f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.58  fof(f491,plain,(
% 0.22/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.58    inference(forward_demodulation,[],[f490,f117])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.58    inference(resolution,[],[f115,f56])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    r1_tarski(k1_xboole_0,sK1)),
% 0.22/0.58    inference(superposition,[],[f45,f98])).
% 0.22/0.58  fof(f98,plain,(
% 0.22/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f94,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 0.22/0.58    inference(superposition,[],[f50,f89])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.58  fof(f490,plain,(
% 0.22/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1))),
% 0.22/0.58    inference(forward_demodulation,[],[f489,f46])).
% 0.22/0.58  fof(f489,plain,(
% 0.22/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0))),
% 0.22/0.58    inference(forward_demodulation,[],[f488,f43])).
% 0.22/0.58  fof(f488,plain,(
% 0.22/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 0.22/0.58    inference(backward_demodulation,[],[f227,f487])).
% 0.22/0.58  fof(f487,plain,(
% 0.22/0.58    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f486,f114])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f107,f46])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1)) )),
% 0.22/0.58    inference(superposition,[],[f64,f90])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.22/0.58  fof(f486,plain,(
% 0.22/0.58    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f479,f46])).
% 0.22/0.58  fof(f479,plain,(
% 0.22/0.58    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(k5_xboole_0(X1,sK1),sK1)) )),
% 0.22/0.58    inference(superposition,[],[f64,f463])).
% 0.22/0.58  fof(f463,plain,(
% 0.22/0.58    sK1 = k3_xboole_0(sK1,sK1)),
% 0.22/0.58    inference(resolution,[],[f461,f56])).
% 0.22/0.58  fof(f461,plain,(
% 0.22/0.58    r1_tarski(sK1,sK1)),
% 0.22/0.58    inference(superposition,[],[f45,f450])).
% 0.22/0.58  fof(f450,plain,(
% 0.22/0.58    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.58    inference(forward_demodulation,[],[f445,f44])).
% 0.22/0.58  fof(f445,plain,(
% 0.22/0.58    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.58    inference(superposition,[],[f50,f427])).
% 0.22/0.58  fof(f427,plain,(
% 0.22/0.58    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.58    inference(superposition,[],[f389,f245])).
% 0.22/0.58  fof(f245,plain,(
% 0.22/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(resolution,[],[f243,f56])).
% 0.22/0.58  fof(f243,plain,(
% 0.22/0.58    r1_tarski(k1_xboole_0,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(superposition,[],[f45,f238])).
% 0.22/0.58  fof(f238,plain,(
% 0.22/0.58    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f234,f43])).
% 0.22/0.58  fof(f234,plain,(
% 0.22/0.58    k4_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(superposition,[],[f50,f171])).
% 0.22/0.58  fof(f171,plain,(
% 0.22/0.58    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.22/0.58    inference(resolution,[],[f169,f56])).
% 0.22/0.58  fof(f169,plain,(
% 0.22/0.58    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.22/0.58    inference(superposition,[],[f45,f103])).
% 0.22/0.58  fof(f389,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))) )),
% 0.22/0.58    inference(superposition,[],[f315,f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.58  fof(f315,plain,(
% 0.22/0.58    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,sK0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f314,f44])).
% 0.22/0.58  fof(f314,plain,(
% 0.22/0.58    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,sK0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f308,f46])).
% 0.22/0.58  fof(f308,plain,(
% 0.22/0.58    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k5_xboole_0(X1,sK0),k1_xboole_0)) )),
% 0.22/0.58    inference(superposition,[],[f64,f292])).
% 0.22/0.58  fof(f292,plain,(
% 0.22/0.58    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.58    inference(forward_demodulation,[],[f286,f43])).
% 0.22/0.58  fof(f286,plain,(
% 0.22/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 0.22/0.58    inference(superposition,[],[f100,f89])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f96,f46])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0))) )),
% 0.22/0.58    inference(superposition,[],[f64,f89])).
% 0.22/0.58  fof(f227,plain,(
% 0.22/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 0.22/0.58    inference(superposition,[],[f51,f206])).
% 0.22/0.58  fof(f206,plain,(
% 0.22/0.58    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(forward_demodulation,[],[f195,f203])).
% 0.22/0.58  fof(f203,plain,(
% 0.22/0.58    sK0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(forward_demodulation,[],[f202,f44])).
% 0.22/0.58  fof(f202,plain,(
% 0.22/0.58    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.58    inference(forward_demodulation,[],[f194,f43])).
% 0.22/0.58  fof(f194,plain,(
% 0.22/0.58    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(superposition,[],[f104,f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(superposition,[],[f51,f90])).
% 0.22/0.58  fof(f195,plain,(
% 0.22/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)),
% 0.22/0.58    inference(superposition,[],[f104,f47])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.58  fof(f267,plain,(
% 0.22/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(resolution,[],[f73,f176])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(subsumption_resolution,[],[f173,f41])).
% 0.22/0.58  fof(f173,plain,(
% 0.22/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(resolution,[],[f170,f53])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f170,plain,(
% 0.22/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.58    inference(resolution,[],[f169,f70])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 0.22/0.58    inference(resolution,[],[f39,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(flattening,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.58    inference(ennf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (15193)------------------------------
% 0.22/0.58  % (15193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (15193)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (15193)Memory used [KB]: 2046
% 0.22/0.58  % (15193)Time elapsed: 0.162 s
% 0.22/0.58  % (15193)------------------------------
% 0.22/0.58  % (15193)------------------------------
% 0.22/0.58  % (15169)Success in time 0.204 s
%------------------------------------------------------------------------------
