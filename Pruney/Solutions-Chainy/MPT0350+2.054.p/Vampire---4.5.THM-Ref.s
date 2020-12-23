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
% DateTime   : Thu Dec  3 12:43:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 964 expanded)
%              Number of leaves         :   20 ( 276 expanded)
%              Depth                    :   34
%              Number of atoms          :  206 (2470 expanded)
%              Number of equality atoms :   92 ( 785 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f666,plain,(
    $false ),
    inference(subsumption_resolution,[],[f665,f246])).

fof(f246,plain,(
    sK0 != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f107,f235])).

fof(f235,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f233,f140])).

fof(f140,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f51,f106])).

fof(f106,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f52,f95])).

fof(f95,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f84,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f84,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f78,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f233,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f51,f155])).

fof(f155,plain,(
    k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f152,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f152,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f52,f142])).

fof(f142,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f141,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f141,plain,(
    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f46,f106])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f107,plain,(
    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f87,f106])).

fof(f87,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f83])).

fof(f83,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f77,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f85,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f82,f68])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f82,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f73,f76])).

fof(f73,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f41,f43])).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f665,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f664,f45])).

fof(f664,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f656,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f656,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f650,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f650,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f648,f620])).

fof(f620,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f619,f140])).

fof(f619,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f573,f48])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f573,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f281,f559])).

fof(f559,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f556,f507])).

fof(f507,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f502,f48])).

fof(f502,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),sK1) ),
    inference(forward_demodulation,[],[f501,f48])).

fof(f501,plain,(
    k5_xboole_0(sK1,sK0) = k5_xboole_0(k2_xboole_0(sK1,sK0),sK1) ),
    inference(forward_demodulation,[],[f494,f45])).

fof(f494,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f232,f44])).

fof(f232,plain,(
    ! [X0] : k5_xboole_0(k2_xboole_0(sK1,sK0),X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f231,f67])).

fof(f231,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[],[f67,f140])).

fof(f556,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f550,f67])).

fof(f550,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f544,f48])).

fof(f544,plain,(
    sK1 = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f543,f45])).

fof(f543,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f492,f538])).

fof(f538,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f528,f48])).

fof(f528,plain,(
    k1_xboole_0 = k5_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
    inference(superposition,[],[f495,f515])).

fof(f515,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f513,f44])).

fof(f513,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f232,f507])).

fof(f495,plain,(
    ! [X1] : k5_xboole_0(k2_xboole_0(sK1,sK0),X1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X1,sK1))) ),
    inference(superposition,[],[f232,f48])).

fof(f492,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f232,f140])).

fof(f281,plain,(
    k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f51,f202])).

fof(f202,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f52,f188])).

fof(f188,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f135,f47])).

fof(f135,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f129,f72])).

fof(f129,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,
    ( r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f108,f53])).

fof(f108,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f83,f106])).

fof(f648,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f51,f560])).

fof(f560,plain,(
    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f202,f559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16542)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (16520)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (16540)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (16526)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (16534)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (16528)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (16546)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (16534)Refutation not found, incomplete strategy% (16534)------------------------------
% 0.20/0.51  % (16534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16534)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16534)Memory used [KB]: 6140
% 0.20/0.51  % (16534)Time elapsed: 0.003 s
% 0.20/0.51  % (16534)------------------------------
% 0.20/0.51  % (16534)------------------------------
% 0.20/0.51  % (16524)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (16523)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (16519)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (16529)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (16522)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (16525)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (16547)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (16530)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16533)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (16536)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (16527)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (16538)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (16541)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (16531)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16544)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (16521)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (16537)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (16548)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (16542)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f666,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f665,f246])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    sK0 != k2_xboole_0(sK1,sK0)),
% 0.20/0.53    inference(superposition,[],[f107,f235])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f233,f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(superposition,[],[f51,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.20/0.53    inference(superposition,[],[f52,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    sK1 = k3_xboole_0(sK0,sK1)),
% 0.20/0.53    inference(superposition,[],[f93,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f88,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    r1_tarski(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f84,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.54    inference(rectify,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f78,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,axiom,(
% 0.20/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f40,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f23])).
% 0.20/0.54  fof(f23,conjecture,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.54  fof(f233,plain,(
% 0.20/0.54    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(superposition,[],[f51,f155])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f152,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    k4_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.54    inference(superposition,[],[f52,f142])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.20/0.54    inference(resolution,[],[f141,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.20/0.54    inference(superposition,[],[f46,f106])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f87,f106])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f86,f40])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f85,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(forward_demodulation,[],[f77,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.54    inference(resolution,[],[f40,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f40,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(superposition,[],[f82,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f73,f76])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f41,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f665,plain,(
% 0.20/0.54    sK0 = k2_xboole_0(sK1,sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f664,f45])).
% 0.20/0.54  fof(f664,plain,(
% 0.20/0.54    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK1,sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f656,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.54  fof(f656,plain,(
% 0.20/0.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 0.20/0.54    inference(superposition,[],[f650,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.54  fof(f650,plain,(
% 0.20/0.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f648,f620])).
% 0.20/0.54  fof(f620,plain,(
% 0.20/0.54    k2_xboole_0(sK1,sK0) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f619,f140])).
% 0.20/0.54  fof(f619,plain,(
% 0.20/0.54    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f573,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.54  fof(f573,plain,(
% 0.20/0.54    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f281,f559])).
% 0.20/0.54  fof(f559,plain,(
% 0.20/0.54    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f556,f507])).
% 0.20/0.54  fof(f507,plain,(
% 0.20/0.54    k5_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))),
% 0.20/0.54    inference(superposition,[],[f502,f48])).
% 0.20/0.54  fof(f502,plain,(
% 0.20/0.54    k5_xboole_0(sK0,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f501,f48])).
% 0.20/0.54  fof(f501,plain,(
% 0.20/0.54    k5_xboole_0(sK1,sK0) = k5_xboole_0(k2_xboole_0(sK1,sK0),sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f494,f45])).
% 0.20/0.54  fof(f494,plain,(
% 0.20/0.54    k5_xboole_0(k2_xboole_0(sK1,sK0),sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.54    inference(superposition,[],[f232,f44])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(k2_xboole_0(sK1,sK0),X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f231,f67])).
% 0.20/0.54  fof(f231,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),X0)) )),
% 0.20/0.54    inference(superposition,[],[f67,f140])).
% 0.20/0.54  fof(f556,plain,(
% 0.20/0.54    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)))),
% 0.20/0.54    inference(superposition,[],[f550,f67])).
% 0.20/0.54  fof(f550,plain,(
% 0.20/0.54    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 0.20/0.54    inference(superposition,[],[f544,f48])).
% 0.20/0.54  fof(f544,plain,(
% 0.20/0.54    sK1 = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f543,f45])).
% 0.20/0.54  fof(f543,plain,(
% 0.20/0.54    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f492,f538])).
% 0.20/0.54  fof(f538,plain,(
% 0.20/0.54    k1_xboole_0 = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 0.20/0.54    inference(superposition,[],[f528,f48])).
% 0.20/0.54  fof(f528,plain,(
% 0.20/0.54    k1_xboole_0 = k5_xboole_0(k2_xboole_0(sK1,sK0),sK0)),
% 0.20/0.54    inference(superposition,[],[f495,f515])).
% 0.20/0.54  fof(f515,plain,(
% 0.20/0.54    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.20/0.54    inference(forward_demodulation,[],[f513,f44])).
% 0.20/0.54  fof(f513,plain,(
% 0.20/0.54    k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))),
% 0.20/0.54    inference(superposition,[],[f232,f507])).
% 0.20/0.54  fof(f495,plain,(
% 0.20/0.54    ( ! [X1] : (k5_xboole_0(k2_xboole_0(sK1,sK0),X1) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(X1,sK1)))) )),
% 0.20/0.54    inference(superposition,[],[f232,f48])).
% 0.20/0.54  fof(f492,plain,(
% 0.20/0.54    k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 0.20/0.54    inference(superposition,[],[f232,f140])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    k2_xboole_0(k5_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))),
% 0.20/0.54    inference(superposition,[],[f51,f202])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    k4_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(superposition,[],[f52,f188])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(superposition,[],[f135,f47])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(resolution,[],[f130,f57])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(resolution,[],[f129,f72])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f124,f42])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f108,f53])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(backward_demodulation,[],[f83,f106])).
% 0.20/0.54  fof(f648,plain,(
% 0.20/0.54    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 0.20/0.54    inference(superposition,[],[f51,f560])).
% 0.20/0.54  fof(f560,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(backward_demodulation,[],[f202,f559])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (16542)------------------------------
% 0.20/0.54  % (16542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16542)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (16542)Memory used [KB]: 2046
% 0.20/0.54  % (16542)Time elapsed: 0.095 s
% 0.20/0.54  % (16542)------------------------------
% 0.20/0.54  % (16542)------------------------------
% 0.20/0.54  % (16518)Success in time 0.18 s
%------------------------------------------------------------------------------
