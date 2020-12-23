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
% DateTime   : Thu Dec  3 12:43:58 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  130 (13096 expanded)
%              Number of leaves         :   21 (3661 expanded)
%              Depth                    :   40
%              Number of atoms          :  219 (38017 expanded)
%              Number of equality atoms :  114 (10283 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(subsumption_resolution,[],[f891,f115])).

fof(f115,plain,(
    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f91,f110])).

fof(f110,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f54,f98])).

fof(f98,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f97,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f97,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f92,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f88,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f88,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,(
    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f89,f87])).

fof(f87,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f81,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f89,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f86,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f86,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f77,f80])).

fof(f77,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f43,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f891,plain,(
    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f890,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f890,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f889,f835])).

fof(f835,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f834,f148])).

fof(f148,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f144,f143])).

fof(f143,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f48,f119])).

fof(f119,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f106,f111])).

fof(f111,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f55,f98])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f106,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f103,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f103,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f55,f97])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f144,plain,(
    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f54,f142])).

fof(f142,plain,(
    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f51,f119])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f834,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f800,f803])).

fof(f803,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f802,f47])).

fof(f802,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f786,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f786,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f606,f60])).

fof(f606,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k3_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f544,f545])).

fof(f545,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(forward_demodulation,[],[f540,f47])).

fof(f540,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f454,f50])).

fof(f454,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f413,f232])).

fof(f232,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f68,f228])).

fof(f228,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f224,f223])).

fof(f223,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f48,f199])).

fof(f199,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f198,f47])).

fof(f198,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f190,f148])).

fof(f190,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f111,f68])).

fof(f224,plain,(
    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f54,f222])).

fof(f222,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f51,f199])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f413,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f68,f396])).

fof(f396,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f379,f211])).

fof(f211,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f191,f199])).

fof(f191,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f111,f50])).

fof(f379,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f150,f50])).

fof(f150,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f68,f148])).

fof(f544,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X3))) ),
    inference(superposition,[],[f55,f454])).

fof(f800,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f546,f606])).

fof(f546,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0 ),
    inference(backward_demodulation,[],[f150,f545])).

fof(f889,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f888,f49])).

fof(f888,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f886,f228])).

fof(f886,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(backward_demodulation,[],[f248,f885])).

fof(f885,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f882,f121])).

fof(f121,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f114,f49])).

fof(f114,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f69,f98])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f882,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(backward_demodulation,[],[f664,f873])).

fof(f873,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f51,f847])).

fof(f847,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f840,f811])).

fof(f811,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f810,f803])).

fof(f810,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f787,f54])).

fof(f787,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f606,f49])).

fof(f840,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f829,f838])).

fof(f838,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f51,f803])).

fof(f829,plain,(
    ! [X2] : k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f828,f54])).

fof(f828,plain,(
    ! [X2] : k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) ),
    inference(forward_demodulation,[],[f795,f803])).

fof(f795,plain,(
    ! [X2] : k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k2_xboole_0(k1_xboole_0,X2),k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) ),
    inference(superposition,[],[f55,f606])).

fof(f664,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK1)),sK1) = k3_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f658,f49])).

fof(f658,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK1),k3_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK1)),sK1) ),
    inference(superposition,[],[f69,f632])).

fof(f632,plain,(
    sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f51,f559])).

fof(f559,plain,(
    k2_xboole_0(sK1,sK1) = k3_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f151,f545])).

fof(f151,plain,(
    k2_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f55,f148])).

fof(f248,plain,(
    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f55,f211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.51  % (1315)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (1315)Refutation not found, incomplete strategy% (1315)------------------------------
% 0.23/0.51  % (1315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (1307)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.53  % (1315)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (1315)Memory used [KB]: 10746
% 0.23/0.54  % (1315)Time elapsed: 0.069 s
% 0.23/0.54  % (1315)------------------------------
% 0.23/0.54  % (1315)------------------------------
% 0.23/0.54  % (1298)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (1318)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (1317)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.56  % (1302)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.56  % (1296)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.56  % (1316)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (1311)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.56  % (1314)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.56  % (1308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.56  % (1309)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.56  % (1312)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.56  % (1300)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.57  % (1301)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.57  % (1322)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.57  % (1319)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.57  % (1320)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.57  % (1310)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.57  % (1299)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.57  % (1310)Refutation not found, incomplete strategy% (1310)------------------------------
% 1.49/0.57  % (1310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (1310)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (1310)Memory used [KB]: 10618
% 1.49/0.57  % (1310)Time elapsed: 0.127 s
% 1.49/0.57  % (1310)------------------------------
% 1.49/0.57  % (1310)------------------------------
% 1.49/0.57  % (1303)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.57  % (1304)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.58  % (1295)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.58  % (1294)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.58  % (1306)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.58  % (1313)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.59  % (1305)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.59  % (1321)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.59  % (1293)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.60  % (1297)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.62  % (1316)Refutation found. Thanks to Tanya!
% 1.49/0.62  % SZS status Theorem for theBenchmark
% 1.49/0.62  % SZS output start Proof for theBenchmark
% 1.49/0.62  fof(f892,plain,(
% 1.49/0.62    $false),
% 1.49/0.62    inference(subsumption_resolution,[],[f891,f115])).
% 1.49/0.62  fof(f115,plain,(
% 1.49/0.62    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(backward_demodulation,[],[f91,f110])).
% 1.49/0.62  fof(f110,plain,(
% 1.49/0.62    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(superposition,[],[f54,f98])).
% 1.49/0.62  fof(f98,plain,(
% 1.49/0.62    sK1 = k3_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(superposition,[],[f97,f49])).
% 1.49/0.62  fof(f49,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f1])).
% 1.49/0.62  fof(f1,axiom,(
% 1.49/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.49/0.62  fof(f97,plain,(
% 1.49/0.62    sK1 = k3_xboole_0(sK1,sK0)),
% 1.49/0.62    inference(resolution,[],[f92,f60])).
% 1.49/0.62  fof(f60,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f30])).
% 1.49/0.62  fof(f30,plain,(
% 1.49/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.62    inference(ennf_transformation,[],[f6])).
% 1.49/0.62  fof(f6,axiom,(
% 1.49/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.62  fof(f92,plain,(
% 1.49/0.62    r1_tarski(sK1,sK0)),
% 1.49/0.62    inference(resolution,[],[f88,f76])).
% 1.49/0.62  fof(f76,plain,(
% 1.49/0.62    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(equality_resolution,[],[f63])).
% 1.49/0.62  fof(f63,plain,(
% 1.49/0.62    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f41])).
% 1.49/0.62  fof(f41,plain,(
% 1.49/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.49/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 1.49/0.62  fof(f40,plain,(
% 1.49/0.62    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.49/0.62    introduced(choice_axiom,[])).
% 1.49/0.62  fof(f39,plain,(
% 1.49/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.49/0.62    inference(rectify,[],[f38])).
% 1.49/0.62  fof(f38,plain,(
% 1.49/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.49/0.62    inference(nnf_transformation,[],[f18])).
% 1.49/0.62  fof(f18,axiom,(
% 1.49/0.62    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.49/0.62  fof(f88,plain,(
% 1.49/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(subsumption_resolution,[],[f82,f44])).
% 1.49/0.62  fof(f44,plain,(
% 1.49/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f24])).
% 1.49/0.62  fof(f24,axiom,(
% 1.49/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.49/0.62  fof(f82,plain,(
% 1.49/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(resolution,[],[f42,f56])).
% 1.49/0.62  fof(f56,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f37])).
% 1.49/0.62  fof(f37,plain,(
% 1.49/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.49/0.62    inference(nnf_transformation,[],[f29])).
% 1.49/0.62  fof(f29,plain,(
% 1.49/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f20])).
% 1.49/0.62  fof(f20,axiom,(
% 1.49/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.49/0.62  fof(f42,plain,(
% 1.49/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(cnf_transformation,[],[f36])).
% 1.49/0.62  fof(f36,plain,(
% 1.49/0.62    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f35])).
% 1.49/0.62  fof(f35,plain,(
% 1.49/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.49/0.62    introduced(choice_axiom,[])).
% 1.49/0.62  fof(f28,plain,(
% 1.49/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f27])).
% 1.49/0.62  fof(f27,negated_conjecture,(
% 1.49/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.49/0.62    inference(negated_conjecture,[],[f26])).
% 1.49/0.62  fof(f26,conjecture,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.49/0.62  fof(f54,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f3])).
% 1.49/0.62  fof(f3,axiom,(
% 1.49/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.62  fof(f91,plain,(
% 1.49/0.62    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(subsumption_resolution,[],[f90,f42])).
% 1.49/0.62  fof(f90,plain,(
% 1.49/0.62    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(subsumption_resolution,[],[f89,f87])).
% 1.49/0.62  fof(f87,plain,(
% 1.49/0.62    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(forward_demodulation,[],[f81,f80])).
% 1.49/0.62  fof(f80,plain,(
% 1.49/0.62    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(resolution,[],[f42,f62])).
% 1.49/0.62  fof(f62,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f32])).
% 1.49/0.62  fof(f32,plain,(
% 1.49/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f22])).
% 1.49/0.62  fof(f22,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.49/0.62  fof(f81,plain,(
% 1.49/0.62    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(resolution,[],[f42,f61])).
% 1.49/0.62  fof(f61,plain,(
% 1.49/0.62    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f31])).
% 1.49/0.62  fof(f31,plain,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f23])).
% 1.49/0.62  fof(f23,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.49/0.62  fof(f89,plain,(
% 1.49/0.62    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.49/0.62    inference(superposition,[],[f86,f70])).
% 1.49/0.62  fof(f70,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f34])).
% 1.49/0.62  fof(f34,plain,(
% 1.49/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(flattening,[],[f33])).
% 1.49/0.62  fof(f33,plain,(
% 1.49/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.49/0.62    inference(ennf_transformation,[],[f25])).
% 1.49/0.62  fof(f25,axiom,(
% 1.49/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.49/0.62  fof(f86,plain,(
% 1.49/0.62    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(backward_demodulation,[],[f77,f80])).
% 1.49/0.62  fof(f77,plain,(
% 1.49/0.62    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f43,f46])).
% 1.49/0.62  fof(f46,plain,(
% 1.49/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.49/0.62    inference(cnf_transformation,[],[f21])).
% 1.49/0.62  fof(f21,axiom,(
% 1.49/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.49/0.62  fof(f43,plain,(
% 1.49/0.62    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.49/0.62    inference(cnf_transformation,[],[f36])).
% 1.49/0.62  fof(f891,plain,(
% 1.49/0.62    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f890,f47])).
% 1.49/0.62  fof(f47,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.62    inference(cnf_transformation,[],[f9])).
% 1.49/0.62  fof(f9,axiom,(
% 1.49/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.62  fof(f890,plain,(
% 1.49/0.62    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.49/0.62    inference(forward_demodulation,[],[f889,f835])).
% 1.49/0.62  fof(f835,plain,(
% 1.49/0.62    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 1.49/0.62    inference(forward_demodulation,[],[f834,f148])).
% 1.49/0.62  fof(f148,plain,(
% 1.49/0.62    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.49/0.62    inference(forward_demodulation,[],[f144,f143])).
% 1.49/0.62  fof(f143,plain,(
% 1.49/0.62    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(superposition,[],[f48,f119])).
% 1.49/0.62  fof(f119,plain,(
% 1.49/0.62    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(backward_demodulation,[],[f106,f111])).
% 1.49/0.62  fof(f111,plain,(
% 1.49/0.62    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(superposition,[],[f55,f98])).
% 1.49/0.62  fof(f55,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f11])).
% 1.49/0.62  fof(f11,axiom,(
% 1.49/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.49/0.62  fof(f106,plain,(
% 1.49/0.62    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.49/0.62    inference(forward_demodulation,[],[f103,f50])).
% 1.49/0.62  fof(f50,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f2])).
% 1.49/0.62  fof(f2,axiom,(
% 1.49/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.49/0.62  fof(f103,plain,(
% 1.49/0.62    k2_xboole_0(sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)),
% 1.49/0.62    inference(superposition,[],[f55,f97])).
% 1.49/0.62  fof(f48,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f8])).
% 1.49/0.62  fof(f8,axiom,(
% 1.49/0.62    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.49/0.62  fof(f144,plain,(
% 1.49/0.62    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(superposition,[],[f54,f142])).
% 1.49/0.62  fof(f142,plain,(
% 1.49/0.62    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(superposition,[],[f51,f119])).
% 1.49/0.62  fof(f51,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.49/0.62    inference(cnf_transformation,[],[f5])).
% 1.49/0.62  fof(f5,axiom,(
% 1.49/0.62    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.49/0.62  fof(f834,plain,(
% 1.49/0.62    k5_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1)),
% 1.49/0.62    inference(forward_demodulation,[],[f800,f803])).
% 1.49/0.62  fof(f803,plain,(
% 1.49/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.49/0.62    inference(forward_demodulation,[],[f802,f47])).
% 1.49/0.62  fof(f802,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.62    inference(subsumption_resolution,[],[f786,f45])).
% 1.49/0.62  fof(f45,plain,(
% 1.49/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f7])).
% 1.49/0.62  fof(f7,axiom,(
% 1.49/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.62  fof(f786,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.62    inference(superposition,[],[f606,f60])).
% 1.49/0.62  fof(f606,plain,(
% 1.49/0.62    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k3_xboole_0(k1_xboole_0,X3))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f544,f545])).
% 1.49/0.62  fof(f545,plain,(
% 1.49/0.62    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.49/0.62    inference(forward_demodulation,[],[f540,f47])).
% 1.49/0.62  fof(f540,plain,(
% 1.49/0.62    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0))) )),
% 1.49/0.62    inference(superposition,[],[f454,f50])).
% 1.49/0.62  fof(f454,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.49/0.62    inference(superposition,[],[f413,f232])).
% 1.49/0.62  fof(f232,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0))) )),
% 1.49/0.62    inference(superposition,[],[f68,f228])).
% 1.49/0.62  fof(f228,plain,(
% 1.49/0.62    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.49/0.62    inference(forward_demodulation,[],[f224,f223])).
% 1.49/0.62  fof(f223,plain,(
% 1.49/0.62    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.49/0.62    inference(superposition,[],[f48,f199])).
% 1.49/0.62  fof(f199,plain,(
% 1.49/0.62    sK0 = k2_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(forward_demodulation,[],[f198,f47])).
% 1.49/0.62  fof(f198,plain,(
% 1.49/0.62    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.49/0.62    inference(forward_demodulation,[],[f190,f148])).
% 1.49/0.62  fof(f190,plain,(
% 1.49/0.62    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(superposition,[],[f111,f68])).
% 1.49/0.62  fof(f224,plain,(
% 1.49/0.62    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,sK0)),
% 1.49/0.62    inference(superposition,[],[f54,f222])).
% 1.49/0.62  fof(f222,plain,(
% 1.49/0.62    sK0 = k3_xboole_0(sK0,sK0)),
% 1.49/0.62    inference(superposition,[],[f51,f199])).
% 1.49/0.62  fof(f68,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f10])).
% 1.49/0.62  fof(f10,axiom,(
% 1.49/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.49/0.62  fof(f413,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))) )),
% 1.49/0.62    inference(superposition,[],[f68,f396])).
% 1.49/0.62  fof(f396,plain,(
% 1.49/0.62    sK0 = k5_xboole_0(k1_xboole_0,sK0)),
% 1.49/0.62    inference(superposition,[],[f379,f211])).
% 1.49/0.62  fof(f211,plain,(
% 1.49/0.62    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f191,f199])).
% 1.49/0.62  fof(f191,plain,(
% 1.49/0.62    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)),
% 1.49/0.62    inference(superposition,[],[f111,f50])).
% 1.49/0.62  fof(f379,plain,(
% 1.49/0.62    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 1.49/0.62    inference(superposition,[],[f150,f50])).
% 1.49/0.62  fof(f150,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.62    inference(superposition,[],[f68,f148])).
% 1.49/0.62  fof(f544,plain,(
% 1.49/0.62    ( ! [X3] : (k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X3)))) )),
% 1.49/0.62    inference(superposition,[],[f55,f454])).
% 1.49/0.62  fof(f800,plain,(
% 1.49/0.62    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK1))),
% 1.49/0.62    inference(superposition,[],[f546,f606])).
% 1.49/0.62  fof(f546,plain,(
% 1.49/0.62    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0) )),
% 1.49/0.62    inference(backward_demodulation,[],[f150,f545])).
% 1.49/0.62  fof(f889,plain,(
% 1.49/0.62    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k1_xboole_0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f888,f49])).
% 1.49/0.62  fof(f888,plain,(
% 1.49/0.62    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k1_xboole_0))),
% 1.49/0.62    inference(forward_demodulation,[],[f886,f228])).
% 1.49/0.62  fof(f886,plain,(
% 1.49/0.62    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 1.49/0.62    inference(backward_demodulation,[],[f248,f885])).
% 1.49/0.62  fof(f885,plain,(
% 1.49/0.62    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f882,f121])).
% 1.49/0.62  fof(f121,plain,(
% 1.49/0.62    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f114,f49])).
% 1.49/0.62  fof(f114,plain,(
% 1.49/0.62    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1)) )),
% 1.49/0.62    inference(superposition,[],[f69,f98])).
% 1.49/0.62  fof(f69,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f4])).
% 1.49/0.62  fof(f4,axiom,(
% 1.49/0.62    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.49/0.62  fof(f882,plain,(
% 1.49/0.62    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 1.49/0.62    inference(backward_demodulation,[],[f664,f873])).
% 1.49/0.62  fof(f873,plain,(
% 1.49/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.49/0.62    inference(superposition,[],[f51,f847])).
% 1.49/0.62  fof(f847,plain,(
% 1.49/0.62    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.49/0.62    inference(forward_demodulation,[],[f840,f811])).
% 1.49/0.62  fof(f811,plain,(
% 1.49/0.62    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.49/0.62    inference(forward_demodulation,[],[f810,f803])).
% 1.49/0.62  fof(f810,plain,(
% 1.49/0.62    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 1.49/0.62    inference(forward_demodulation,[],[f787,f54])).
% 1.49/0.62  fof(f787,plain,(
% 1.49/0.62    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.49/0.62    inference(superposition,[],[f606,f49])).
% 1.49/0.62  fof(f840,plain,(
% 1.49/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)) )),
% 1.49/0.62    inference(backward_demodulation,[],[f829,f838])).
% 1.49/0.62  fof(f838,plain,(
% 1.49/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.62    inference(superposition,[],[f51,f803])).
% 1.49/0.62  fof(f829,plain,(
% 1.49/0.62    ( ! [X2] : (k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f828,f54])).
% 1.49/0.62  fof(f828,plain,(
% 1.49/0.62    ( ! [X2] : (k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f795,f803])).
% 1.49/0.62  fof(f795,plain,(
% 1.49/0.62    ( ! [X2] : (k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k2_xboole_0(k1_xboole_0,X2),k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2)))) )),
% 1.49/0.62    inference(superposition,[],[f55,f606])).
% 1.49/0.62  fof(f664,plain,(
% 1.49/0.62    ( ! [X1] : (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK1)),sK1) = k3_xboole_0(k3_xboole_0(sK1,sK1),k5_xboole_0(X1,sK1))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f658,f49])).
% 1.49/0.62  fof(f658,plain,(
% 1.49/0.62    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK1),k3_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK1)),sK1)) )),
% 1.49/0.62    inference(superposition,[],[f69,f632])).
% 1.49/0.62  fof(f632,plain,(
% 1.49/0.62    sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))),
% 1.49/0.62    inference(superposition,[],[f51,f559])).
% 1.49/0.62  fof(f559,plain,(
% 1.49/0.62    k2_xboole_0(sK1,sK1) = k3_xboole_0(sK1,sK1)),
% 1.49/0.62    inference(backward_demodulation,[],[f151,f545])).
% 1.49/0.62  fof(f151,plain,(
% 1.49/0.62    k2_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1))),
% 1.49/0.62    inference(superposition,[],[f55,f148])).
% 1.49/0.62  fof(f248,plain,(
% 1.49/0.62    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.49/0.62    inference(superposition,[],[f55,f211])).
% 1.49/0.62  % SZS output end Proof for theBenchmark
% 1.49/0.62  % (1316)------------------------------
% 1.49/0.62  % (1316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.62  % (1316)Termination reason: Refutation
% 1.49/0.62  
% 1.49/0.62  % (1316)Memory used [KB]: 2174
% 1.49/0.62  % (1316)Time elapsed: 0.170 s
% 1.49/0.62  % (1316)------------------------------
% 1.49/0.62  % (1316)------------------------------
% 1.49/0.62  % (1292)Success in time 0.24 s
%------------------------------------------------------------------------------
