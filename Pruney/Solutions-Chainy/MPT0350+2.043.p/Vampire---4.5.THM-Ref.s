%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:56 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  114 (1015 expanded)
%              Number of leaves         :   21 ( 282 expanded)
%              Depth                    :   25
%              Number of atoms          :  203 (2964 expanded)
%              Number of equality atoms :   96 ( 787 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f654,f121])).

fof(f121,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f92,f115])).

fof(f115,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f61,f103])).

fof(f103,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f102,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f102,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f96,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f93,f83])).

fof(f83,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f88,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f92,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f84,f87])).

fof(f87,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f48,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f654,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f572,f630])).

fof(f630,plain,(
    sK0 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f629,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f629,plain,(
    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f540,f583])).

fof(f583,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f529,f52])).

fof(f529,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f203,f515])).

fof(f515,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f220,f514])).

fof(f514,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f512,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f512,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f62,f510])).

fof(f510,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f509,f103])).

fof(f509,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f492,f57])).

fof(f492,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f444,f52])).

fof(f444,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k4_xboole_0(sK1,X1) ),
    inference(forward_demodulation,[],[f430,f61])).

fof(f430,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f125,f57])).

fof(f125,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f118,f57])).

fof(f118,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f76,f103])).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f220,plain,(
    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f169,f212])).

fof(f212,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f135,f57])).

fof(f135,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f131,f68])).

fof(f131,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f56,f107])).

fof(f107,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f61,f102])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f169,plain,(
    k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f62,f133])).

fof(f133,plain,(
    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f132,f103])).

fof(f132,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f130,f57])).

fof(f130,plain,(
    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f62,f107])).

fof(f203,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f116,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f116,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f63,f103])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f540,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f303,f515])).

fof(f303,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f232,f296])).

fof(f296,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f112,f102])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f109,f57])).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f76,f102])).

fof(f232,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f63,f203])).

fof(f572,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f440,f515])).

fof(f440,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f285,f439])).

fof(f439,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f438,f303])).

fof(f438,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f235,f428])).

fof(f428,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f125,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f235,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f63,f204])).

fof(f204,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f116,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f285,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f85,f160])).

fof(f160,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f156,f49])).

fof(f156,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f153,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f153,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f151,f82])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f151,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f56,f115])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (703)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (724)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (705)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (707)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (720)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (706)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (719)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (719)Refutation not found, incomplete strategy% (719)------------------------------
% 0.22/0.52  % (719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (719)Memory used [KB]: 10618
% 0.22/0.52  % (719)Time elapsed: 0.108 s
% 0.22/0.52  % (719)------------------------------
% 0.22/0.52  % (719)------------------------------
% 0.22/0.52  % (728)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (713)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (721)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (727)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (702)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (704)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (729)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (709)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (716)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (712)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (714)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (723)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (715)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (708)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (725)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (712)Refutation not found, incomplete strategy% (712)------------------------------
% 0.22/0.53  % (712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (712)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (712)Memory used [KB]: 10618
% 0.22/0.53  % (712)Time elapsed: 0.117 s
% 0.22/0.53  % (712)------------------------------
% 0.22/0.53  % (712)------------------------------
% 0.22/0.53  % (724)Refutation not found, incomplete strategy% (724)------------------------------
% 0.22/0.53  % (724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (724)Memory used [KB]: 10746
% 0.22/0.53  % (724)Time elapsed: 0.106 s
% 0.22/0.53  % (724)------------------------------
% 0.22/0.53  % (724)------------------------------
% 0.22/0.53  % (730)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (710)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (731)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (717)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (726)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (722)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (713)Refutation not found, incomplete strategy% (713)------------------------------
% 0.22/0.54  % (713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (713)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (713)Memory used [KB]: 10618
% 0.22/0.54  % (713)Time elapsed: 0.141 s
% 0.22/0.54  % (713)------------------------------
% 0.22/0.54  % (713)------------------------------
% 1.43/0.55  % (718)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (711)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.56  % (717)Refutation not found, incomplete strategy% (717)------------------------------
% 1.43/0.56  % (717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (717)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (717)Memory used [KB]: 6140
% 1.43/0.56  % (717)Time elapsed: 0.003 s
% 1.43/0.56  % (717)------------------------------
% 1.43/0.56  % (717)------------------------------
% 1.66/0.58  % (725)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f655,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(subsumption_resolution,[],[f654,f121])).
% 1.66/0.58  fof(f121,plain,(
% 1.66/0.58    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.66/0.58    inference(backward_demodulation,[],[f92,f115])).
% 1.66/0.58  fof(f115,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(superposition,[],[f61,f103])).
% 1.66/0.58  fof(f103,plain,(
% 1.66/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(superposition,[],[f102,f57])).
% 1.66/0.58  fof(f57,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f1])).
% 1.66/0.58  fof(f1,axiom,(
% 1.66/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.58  fof(f102,plain,(
% 1.66/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 1.66/0.58    inference(resolution,[],[f96,f68])).
% 1.66/0.58  fof(f68,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f32])).
% 1.66/0.58  fof(f32,plain,(
% 1.66/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f7])).
% 1.66/0.58  fof(f7,axiom,(
% 1.66/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.66/0.58  fof(f96,plain,(
% 1.66/0.58    r1_tarski(sK1,sK0)),
% 1.66/0.58    inference(resolution,[],[f93,f83])).
% 1.66/0.58  fof(f83,plain,(
% 1.66/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.66/0.58    inference(equality_resolution,[],[f70])).
% 1.66/0.58  fof(f70,plain,(
% 1.66/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f46])).
% 1.66/0.58  fof(f46,plain,(
% 1.66/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f44,plain,(
% 1.66/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.66/0.58    inference(rectify,[],[f43])).
% 1.66/0.58  fof(f43,plain,(
% 1.66/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.66/0.58    inference(nnf_transformation,[],[f20])).
% 1.66/0.58  fof(f20,axiom,(
% 1.66/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.66/0.58  fof(f93,plain,(
% 1.66/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(subsumption_resolution,[],[f88,f49])).
% 1.66/0.58  fof(f49,plain,(
% 1.66/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f25])).
% 1.66/0.58  fof(f25,axiom,(
% 1.66/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.66/0.58  fof(f88,plain,(
% 1.66/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(resolution,[],[f47,f64])).
% 1.66/0.58  fof(f64,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f42])).
% 1.66/0.58  fof(f42,plain,(
% 1.66/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.66/0.58    inference(nnf_transformation,[],[f31])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f22])).
% 1.66/0.58  fof(f22,axiom,(
% 1.66/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.66/0.58  fof(f47,plain,(
% 1.66/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(cnf_transformation,[],[f37])).
% 1.66/0.58  fof(f37,plain,(
% 1.66/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f36])).
% 1.66/0.58  fof(f36,plain,(
% 1.66/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f28])).
% 1.66/0.58  fof(f28,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.66/0.58    inference(negated_conjecture,[],[f27])).
% 1.66/0.58  fof(f27,conjecture,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.66/0.58  fof(f61,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f5])).
% 1.66/0.58  fof(f5,axiom,(
% 1.66/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.58  fof(f92,plain,(
% 1.66/0.58    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.66/0.58    inference(backward_demodulation,[],[f84,f87])).
% 1.66/0.58  fof(f87,plain,(
% 1.66/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(resolution,[],[f47,f69])).
% 1.66/0.58  fof(f69,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f33])).
% 1.66/0.58  fof(f33,plain,(
% 1.66/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f24])).
% 1.66/0.58  fof(f24,axiom,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.66/0.58  fof(f84,plain,(
% 1.66/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f48,f50])).
% 1.66/0.58  fof(f50,plain,(
% 1.66/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f23,axiom,(
% 1.66/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.66/0.58  fof(f48,plain,(
% 1.66/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.66/0.58    inference(cnf_transformation,[],[f37])).
% 1.66/0.58  fof(f654,plain,(
% 1.66/0.58    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f572,f630])).
% 1.66/0.58  fof(f630,plain,(
% 1.66/0.58    sK0 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f629,f52])).
% 1.66/0.58  fof(f52,plain,(
% 1.66/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f11])).
% 1.66/0.58  fof(f11,axiom,(
% 1.66/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.66/0.58  fof(f629,plain,(
% 1.66/0.58    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f540,f583])).
% 1.66/0.58  fof(f583,plain,(
% 1.66/0.58    sK0 = k2_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(forward_demodulation,[],[f529,f52])).
% 1.66/0.58  fof(f529,plain,(
% 1.66/0.58    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.58    inference(backward_demodulation,[],[f203,f515])).
% 1.66/0.58  fof(f515,plain,(
% 1.66/0.58    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.66/0.58    inference(backward_demodulation,[],[f220,f514])).
% 1.66/0.58  fof(f514,plain,(
% 1.66/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.66/0.58    inference(forward_demodulation,[],[f512,f51])).
% 1.66/0.58  fof(f51,plain,(
% 1.66/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.66/0.58  fof(f512,plain,(
% 1.66/0.58    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.58    inference(superposition,[],[f62,f510])).
% 1.66/0.58  fof(f510,plain,(
% 1.66/0.58    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f509,f103])).
% 1.66/0.58  fof(f509,plain,(
% 1.66/0.58    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.58    inference(forward_demodulation,[],[f492,f57])).
% 1.66/0.58  fof(f492,plain,(
% 1.66/0.58    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.66/0.58    inference(superposition,[],[f444,f52])).
% 1.66/0.58  fof(f444,plain,(
% 1.66/0.58    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k4_xboole_0(sK1,X1)) )),
% 1.66/0.58    inference(forward_demodulation,[],[f430,f61])).
% 1.66/0.58  fof(f430,plain,(
% 1.66/0.58    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) )),
% 1.66/0.58    inference(superposition,[],[f125,f57])).
% 1.66/0.58  fof(f125,plain,(
% 1.66/0.58    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 1.66/0.58    inference(forward_demodulation,[],[f118,f57])).
% 1.66/0.58  fof(f118,plain,(
% 1.66/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.66/0.58    inference(superposition,[],[f76,f103])).
% 1.66/0.58  fof(f76,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f6])).
% 1.66/0.58  fof(f6,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.66/0.58  fof(f62,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f10])).
% 1.66/0.58  fof(f10,axiom,(
% 1.66/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.58  fof(f220,plain,(
% 1.66/0.58    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)),
% 1.66/0.58    inference(backward_demodulation,[],[f169,f212])).
% 1.66/0.58  fof(f212,plain,(
% 1.66/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(superposition,[],[f135,f57])).
% 1.66/0.58  fof(f135,plain,(
% 1.66/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 1.66/0.58    inference(resolution,[],[f131,f68])).
% 1.66/0.58  fof(f131,plain,(
% 1.66/0.58    r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 1.66/0.58    inference(superposition,[],[f56,f107])).
% 1.66/0.58  fof(f107,plain,(
% 1.66/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.66/0.58    inference(superposition,[],[f61,f102])).
% 1.66/0.58  fof(f56,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f9])).
% 1.66/0.58  fof(f9,axiom,(
% 1.66/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.66/0.58  fof(f169,plain,(
% 1.66/0.58    k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK1)),
% 1.66/0.58    inference(superposition,[],[f62,f133])).
% 1.66/0.58  fof(f133,plain,(
% 1.66/0.58    sK1 = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f132,f103])).
% 1.66/0.58  fof(f132,plain,(
% 1.66/0.58    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f130,f57])).
% 1.66/0.58  fof(f130,plain,(
% 1.66/0.58    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(superposition,[],[f62,f107])).
% 1.66/0.58  fof(f203,plain,(
% 1.66/0.58    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(superposition,[],[f116,f75])).
% 1.66/0.58  fof(f75,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f12])).
% 1.66/0.58  fof(f12,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.66/0.58  fof(f116,plain,(
% 1.66/0.58    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(superposition,[],[f63,f103])).
% 1.66/0.58  fof(f63,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f13])).
% 1.66/0.58  fof(f13,axiom,(
% 1.66/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.66/0.58  fof(f540,plain,(
% 1.66/0.58    k2_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.66/0.58    inference(backward_demodulation,[],[f303,f515])).
% 1.66/0.58  fof(f303,plain,(
% 1.66/0.58    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(backward_demodulation,[],[f232,f296])).
% 1.66/0.58  fof(f296,plain,(
% 1.66/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(superposition,[],[f112,f102])).
% 1.66/0.58  fof(f112,plain,(
% 1.66/0.58    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK1,X0))) )),
% 1.66/0.58    inference(forward_demodulation,[],[f109,f57])).
% 1.66/0.58  fof(f109,plain,(
% 1.66/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK1,X0),sK0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK0))) )),
% 1.66/0.58    inference(superposition,[],[f76,f102])).
% 1.66/0.58  fof(f232,plain,(
% 1.66/0.58    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 1.66/0.58    inference(superposition,[],[f63,f203])).
% 1.66/0.58  fof(f572,plain,(
% 1.66/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.58    inference(backward_demodulation,[],[f440,f515])).
% 1.66/0.58  fof(f440,plain,(
% 1.66/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(backward_demodulation,[],[f285,f439])).
% 1.66/0.58  fof(f439,plain,(
% 1.66/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(forward_demodulation,[],[f438,f303])).
% 1.66/0.58  fof(f438,plain,(
% 1.66/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 1.66/0.58    inference(backward_demodulation,[],[f235,f428])).
% 1.66/0.58  fof(f428,plain,(
% 1.66/0.58    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.66/0.58    inference(superposition,[],[f125,f55])).
% 1.66/0.58  fof(f55,plain,(
% 1.66/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.66/0.58    inference(rectify,[],[f4])).
% 1.66/0.58  fof(f4,axiom,(
% 1.66/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.66/0.58  fof(f235,plain,(
% 1.66/0.58    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.66/0.58    inference(superposition,[],[f63,f204])).
% 1.66/0.58  fof(f204,plain,(
% 1.66/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)),
% 1.66/0.58    inference(superposition,[],[f116,f58])).
% 1.66/0.58  fof(f58,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f2])).
% 1.66/0.58  fof(f2,axiom,(
% 1.66/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.66/0.58  fof(f285,plain,(
% 1.66/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.66/0.58    inference(resolution,[],[f85,f160])).
% 1.66/0.58  fof(f160,plain,(
% 1.66/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(subsumption_resolution,[],[f156,f49])).
% 1.66/0.58  fof(f156,plain,(
% 1.66/0.58    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(resolution,[],[f153,f65])).
% 1.66/0.58  fof(f65,plain,(
% 1.66/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f42])).
% 1.66/0.58  fof(f153,plain,(
% 1.66/0.58    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(resolution,[],[f151,f82])).
% 1.66/0.58  fof(f82,plain,(
% 1.66/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.66/0.58    inference(equality_resolution,[],[f71])).
% 1.66/0.58  fof(f71,plain,(
% 1.66/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f46])).
% 1.66/0.58  fof(f151,plain,(
% 1.66/0.58    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 1.66/0.58    inference(superposition,[],[f56,f115])).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)) )),
% 1.66/0.58    inference(resolution,[],[f47,f77])).
% 1.66/0.58  fof(f77,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f35])).
% 1.66/0.58  fof(f35,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(flattening,[],[f34])).
% 1.66/0.58  fof(f34,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.66/0.58    inference(ennf_transformation,[],[f26])).
% 1.66/0.58  fof(f26,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.66/0.58  % SZS output end Proof for theBenchmark
% 1.66/0.58  % (725)------------------------------
% 1.66/0.58  % (725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (725)Termination reason: Refutation
% 1.66/0.58  
% 1.66/0.58  % (725)Memory used [KB]: 2174
% 1.66/0.58  % (725)Time elapsed: 0.173 s
% 1.66/0.58  % (725)------------------------------
% 1.66/0.58  % (725)------------------------------
% 1.66/0.60  % (701)Success in time 0.237 s
%------------------------------------------------------------------------------
