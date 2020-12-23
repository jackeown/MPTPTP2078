%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:16 EST 2020

% Result     : Theorem 5.22s
% Output     : Refutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 333 expanded)
%              Number of leaves         :   19 (  88 expanded)
%              Depth                    :   27
%              Number of atoms          :  181 ( 705 expanded)
%              Number of equality atoms :   28 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10000,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9985,f892])).

fof(f892,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f888,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f888,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f886,f881])).

fof(f881,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f886,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f40,f880])).

fof(f880,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f9985,plain,(
    r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f48,f9945])).

fof(f9945,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f9944,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f9944,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f9874,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f9874,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f51,f9792])).

fof(f9792,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f9746,f9739])).

fof(f9739,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(resolution,[],[f9734,f1923])).

fof(f1923,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,X6)
      | k1_xboole_0 = k4_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f595,f181])).

fof(f181,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f60,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f595,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f71,f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f9734,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(sK1,sK2),X1) ),
    inference(resolution,[],[f9728,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f9728,plain,(
    ! [X2] : ~ r2_hidden(X2,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f9724,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f9724,plain,(
    v1_xboole_0(k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f9717,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f9717,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | v1_xboole_0(k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f9666,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f9666,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f9579,f896])).

fof(f896,plain,(
    ! [X28] :
      ( ~ r1_tarski(X28,k4_xboole_0(sK0,sK2))
      | r1_tarski(X28,k4_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f891,f892])).

fof(f891,plain,(
    ! [X28] :
      ( r1_tarski(X28,k4_xboole_0(sK0,sK1))
      | ~ r1_tarski(X28,k4_xboole_0(sK0,sK2))
      | r1_tarski(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f883,f881])).

fof(f883,plain,(
    ! [X28] :
      ( ~ r1_tarski(X28,k4_xboole_0(sK0,sK2))
      | r1_tarski(X28,k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f296,f880])).

fof(f296,plain,(
    ! [X28] :
      ( ~ r1_tarski(X28,k3_subset_1(sK0,sK2))
      | r1_tarski(X28,k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f9579,plain,(
    ! [X59] : r1_tarski(k4_xboole_0(sK1,X59),k4_xboole_0(sK0,X59)) ),
    inference(resolution,[],[f598,f5308])).

fof(f5308,plain,(
    ! [X10] : r1_tarski(sK1,k2_xboole_0(X10,sK0)) ),
    inference(superposition,[],[f5270,f50])).

fof(f5270,plain,(
    ! [X20] : r1_tarski(sK1,k2_xboole_0(sK0,X20)) ),
    inference(superposition,[],[f85,f3805])).

fof(f3805,plain,(
    ! [X30] : k2_xboole_0(sK0,X30) = k2_xboole_0(k2_xboole_0(sK0,X30),sK1) ),
    inference(forward_demodulation,[],[f3753,f45])).

fof(f3753,plain,(
    ! [X30] : k2_xboole_0(k2_xboole_0(sK0,X30),sK1) = k2_xboole_0(k2_xboole_0(sK0,X30),k1_xboole_0) ),
    inference(superposition,[],[f51,f3665])).

fof(f3665,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,X7)) ),
    inference(resolution,[],[f3657,f181])).

fof(f3657,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK0,X0)),k1_xboole_0) ),
    inference(resolution,[],[f3066,f48])).

fof(f3066,plain,(
    ! [X17] :
      ( ~ r1_tarski(sK0,X17)
      | r1_tarski(k4_xboole_0(sK1,X17),k1_xboole_0) ) ),
    inference(superposition,[],[f70,f3022])).

fof(f3022,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f1923,f106])).

fof(f106,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f104,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f104,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f101,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f85,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f48,f50])).

fof(f598,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X10,k2_xboole_0(X8,X9))
      | r1_tarski(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8)) ) ),
    inference(superposition,[],[f71,f51])).

fof(f9746,plain,(
    ! [X10] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X10) ),
    inference(resolution,[],[f9734,f179])).

fof(f179,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f60,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (3966)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (3967)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (3976)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (3980)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (3971)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (3982)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (3975)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (3991)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (3972)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (3964)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (3988)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.54  % (3968)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.54  % (3986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.54  % (3992)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.54  % (3979)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.55  % (3973)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (3965)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.55  % (3970)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.55  % (3987)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (3993)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (3985)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (3974)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.56  % (3989)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.56  % (3978)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.56  % (3990)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.56  % (3969)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.57  % (3984)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.57  % (3981)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.58  % (3983)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.58  % (3977)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 3.74/0.86  % (3969)Time limit reached!
% 3.74/0.86  % (3969)------------------------------
% 3.74/0.86  % (3969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.86  % (3969)Termination reason: Time limit
% 3.74/0.86  
% 3.74/0.86  % (3969)Memory used [KB]: 8059
% 3.74/0.86  % (3969)Time elapsed: 0.423 s
% 3.74/0.86  % (3969)------------------------------
% 3.74/0.86  % (3969)------------------------------
% 3.74/0.91  % (3965)Time limit reached!
% 3.74/0.91  % (3965)------------------------------
% 3.74/0.91  % (3965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.91  % (3965)Termination reason: Time limit
% 3.74/0.91  % (3965)Termination phase: Saturation
% 3.74/0.91  
% 3.74/0.91  % (3965)Memory used [KB]: 7419
% 3.74/0.91  % (3965)Time elapsed: 0.500 s
% 3.74/0.91  % (3965)------------------------------
% 3.74/0.91  % (3965)------------------------------
% 3.74/0.92  % (3964)Time limit reached!
% 3.74/0.92  % (3964)------------------------------
% 3.74/0.92  % (3964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.92  % (3964)Termination reason: Time limit
% 3.74/0.92  
% 3.74/0.92  % (3964)Memory used [KB]: 3837
% 3.74/0.92  % (3964)Time elapsed: 0.517 s
% 3.74/0.92  % (3964)------------------------------
% 3.74/0.92  % (3964)------------------------------
% 4.35/0.93  % (3981)Time limit reached!
% 4.35/0.93  % (3981)------------------------------
% 4.35/0.93  % (3981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (3981)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (3981)Memory used [KB]: 12665
% 4.35/0.93  % (3981)Time elapsed: 0.517 s
% 4.35/0.93  % (3981)------------------------------
% 4.35/0.93  % (3981)------------------------------
% 4.35/0.93  % (3976)Time limit reached!
% 4.35/0.93  % (3976)------------------------------
% 4.35/0.93  % (3976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (3976)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (3976)Memory used [KB]: 10362
% 4.35/0.93  % (3976)Time elapsed: 0.528 s
% 4.35/0.93  % (3976)------------------------------
% 4.35/0.93  % (3976)------------------------------
% 4.35/0.94  % (3974)Time limit reached!
% 4.35/0.94  % (3974)------------------------------
% 4.35/0.94  % (3974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.94  % (3974)Termination reason: Time limit
% 4.35/0.94  
% 4.35/0.94  % (3974)Memory used [KB]: 11001
% 4.35/0.94  % (3974)Time elapsed: 0.513 s
% 4.35/0.94  % (3974)------------------------------
% 4.35/0.94  % (3974)------------------------------
% 4.76/0.99  % (3994)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.76/1.02  % (3992)Time limit reached!
% 4.76/1.02  % (3992)------------------------------
% 4.76/1.02  % (3992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.02  % (3992)Termination reason: Time limit
% 4.76/1.02  % (3992)Termination phase: Saturation
% 4.76/1.02  
% 4.76/1.02  % (3992)Memory used [KB]: 8443
% 4.76/1.02  % (3992)Time elapsed: 0.600 s
% 4.76/1.02  % (3992)------------------------------
% 4.76/1.02  % (3992)------------------------------
% 4.76/1.04  % (3971)Time limit reached!
% 4.76/1.04  % (3971)------------------------------
% 4.76/1.04  % (3971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.04  % (3995)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.76/1.04  % (3996)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.76/1.04  % (3980)Time limit reached!
% 4.76/1.04  % (3980)------------------------------
% 4.76/1.04  % (3980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.04  % (3980)Termination reason: Time limit
% 4.76/1.04  
% 4.76/1.04  % (3980)Memory used [KB]: 17654
% 4.76/1.04  % (3980)Time elapsed: 0.638 s
% 4.76/1.04  % (3980)------------------------------
% 4.76/1.04  % (3980)------------------------------
% 4.76/1.05  % (3999)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.22/1.06  % (3971)Termination reason: Time limit
% 5.22/1.06  
% 5.22/1.06  % (3971)Memory used [KB]: 10234
% 5.22/1.06  % (3971)Time elapsed: 0.619 s
% 5.22/1.06  % (3971)------------------------------
% 5.22/1.06  % (3971)------------------------------
% 5.22/1.06  % (3970)Refutation found. Thanks to Tanya!
% 5.22/1.06  % SZS status Theorem for theBenchmark
% 5.22/1.06  % SZS output start Proof for theBenchmark
% 5.22/1.06  fof(f10000,plain,(
% 5.22/1.06    $false),
% 5.22/1.06    inference(subsumption_resolution,[],[f9985,f892])).
% 5.22/1.06  fof(f892,plain,(
% 5.22/1.06    ~r1_tarski(sK1,sK2)),
% 5.22/1.06    inference(subsumption_resolution,[],[f888,f70])).
% 5.22/1.06  fof(f70,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f32])).
% 5.22/1.06  fof(f32,plain,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 5.22/1.06    inference(ennf_transformation,[],[f10])).
% 5.22/1.06  fof(f10,axiom,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 5.22/1.06  fof(f888,plain,(
% 5.22/1.06    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 5.22/1.06    inference(backward_demodulation,[],[f886,f881])).
% 5.22/1.06  fof(f881,plain,(
% 5.22/1.06    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 5.22/1.06    inference(resolution,[],[f57,f42])).
% 5.22/1.06  fof(f42,plain,(
% 5.22/1.06    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.22/1.06    inference(cnf_transformation,[],[f24])).
% 5.22/1.06  fof(f24,plain,(
% 5.22/1.06    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.06    inference(ennf_transformation,[],[f23])).
% 5.22/1.06  fof(f23,negated_conjecture,(
% 5.22/1.06    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 5.22/1.06    inference(negated_conjecture,[],[f22])).
% 5.22/1.06  fof(f22,conjecture,(
% 5.22/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 5.22/1.06  fof(f57,plain,(
% 5.22/1.06    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f28])).
% 5.22/1.06  fof(f28,plain,(
% 5.22/1.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.06    inference(ennf_transformation,[],[f20])).
% 5.22/1.06  fof(f20,axiom,(
% 5.22/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 5.22/1.06  fof(f886,plain,(
% 5.22/1.06    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 5.22/1.06    inference(backward_demodulation,[],[f40,f880])).
% 5.22/1.06  fof(f880,plain,(
% 5.22/1.06    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 5.22/1.06    inference(resolution,[],[f57,f41])).
% 5.22/1.06  fof(f41,plain,(
% 5.22/1.06    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 5.22/1.06    inference(cnf_transformation,[],[f24])).
% 5.22/1.06  fof(f40,plain,(
% 5.22/1.06    ~r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 5.22/1.06    inference(cnf_transformation,[],[f24])).
% 5.22/1.06  fof(f9985,plain,(
% 5.22/1.06    r1_tarski(sK1,sK2)),
% 5.22/1.06    inference(superposition,[],[f48,f9945])).
% 5.22/1.06  fof(f9945,plain,(
% 5.22/1.06    sK2 = k2_xboole_0(sK1,sK2)),
% 5.22/1.06    inference(forward_demodulation,[],[f9944,f45])).
% 5.22/1.06  fof(f45,plain,(
% 5.22/1.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.22/1.06    inference(cnf_transformation,[],[f6])).
% 5.22/1.06  fof(f6,axiom,(
% 5.22/1.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.22/1.06  fof(f9944,plain,(
% 5.22/1.06    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 5.22/1.06    inference(forward_demodulation,[],[f9874,f50])).
% 5.22/1.06  fof(f50,plain,(
% 5.22/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f1])).
% 5.22/1.06  fof(f1,axiom,(
% 5.22/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.22/1.06  fof(f9874,plain,(
% 5.22/1.06    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 5.22/1.06    inference(superposition,[],[f51,f9792])).
% 5.22/1.06  fof(f9792,plain,(
% 5.22/1.06    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 5.22/1.06    inference(forward_demodulation,[],[f9746,f9739])).
% 5.22/1.06  fof(f9739,plain,(
% 5.22/1.06    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) )),
% 5.22/1.06    inference(resolution,[],[f9734,f1923])).
% 5.22/1.06  fof(f1923,plain,(
% 5.22/1.06    ( ! [X6,X5] : (~r1_tarski(X5,X6) | k1_xboole_0 = k4_xboole_0(X5,X6)) )),
% 5.22/1.06    inference(resolution,[],[f595,f181])).
% 5.22/1.06  fof(f181,plain,(
% 5.22/1.06    ( ! [X6] : (~r1_tarski(X6,k1_xboole_0) | k1_xboole_0 = X6) )),
% 5.22/1.06    inference(resolution,[],[f60,f44])).
% 5.22/1.06  fof(f44,plain,(
% 5.22/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f8])).
% 5.22/1.06  fof(f8,axiom,(
% 5.22/1.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.22/1.06  fof(f60,plain,(
% 5.22/1.06    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 5.22/1.06    inference(cnf_transformation,[],[f4])).
% 5.22/1.06  fof(f4,axiom,(
% 5.22/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.22/1.06  fof(f595,plain,(
% 5.22/1.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X1,X0)) )),
% 5.22/1.06    inference(superposition,[],[f71,f45])).
% 5.22/1.06  fof(f71,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f33])).
% 5.22/1.06  fof(f33,plain,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.22/1.06    inference(ennf_transformation,[],[f13])).
% 5.22/1.06  fof(f13,axiom,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 5.22/1.06  fof(f9734,plain,(
% 5.22/1.06    ( ! [X1] : (r1_tarski(k4_xboole_0(sK1,sK2),X1)) )),
% 5.22/1.06    inference(resolution,[],[f9728,f62])).
% 5.22/1.06  fof(f62,plain,(
% 5.22/1.06    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f29])).
% 5.22/1.06  fof(f29,plain,(
% 5.22/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 5.22/1.06    inference(ennf_transformation,[],[f3])).
% 5.22/1.06  fof(f3,axiom,(
% 5.22/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 5.22/1.06  fof(f9728,plain,(
% 5.22/1.06    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK1,sK2))) )),
% 5.22/1.06    inference(resolution,[],[f9724,f47])).
% 5.22/1.06  fof(f47,plain,(
% 5.22/1.06    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f2])).
% 5.22/1.06  fof(f2,axiom,(
% 5.22/1.06    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 5.22/1.06  fof(f9724,plain,(
% 5.22/1.06    v1_xboole_0(k4_xboole_0(sK1,sK2))),
% 5.22/1.06    inference(subsumption_resolution,[],[f9717,f49])).
% 5.22/1.06  fof(f49,plain,(
% 5.22/1.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f11])).
% 5.22/1.06  fof(f11,axiom,(
% 5.22/1.06    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.22/1.06  fof(f9717,plain,(
% 5.22/1.06    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | v1_xboole_0(k4_xboole_0(sK1,sK2))),
% 5.22/1.06    inference(resolution,[],[f9666,f111])).
% 5.22/1.06  fof(f111,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1) | v1_xboole_0(X0)) )),
% 5.22/1.06    inference(resolution,[],[f68,f56])).
% 5.22/1.06  fof(f56,plain,(
% 5.22/1.06    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f27])).
% 5.22/1.06  fof(f27,plain,(
% 5.22/1.06    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 5.22/1.06    inference(flattening,[],[f26])).
% 5.22/1.06  fof(f26,plain,(
% 5.22/1.06    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 5.22/1.06    inference(ennf_transformation,[],[f14])).
% 5.22/1.06  fof(f14,axiom,(
% 5.22/1.06    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 5.22/1.06  fof(f68,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f30])).
% 5.22/1.06  fof(f30,plain,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 5.22/1.06    inference(ennf_transformation,[],[f16])).
% 5.22/1.06  fof(f16,axiom,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 5.22/1.06  fof(f9666,plain,(
% 5.22/1.06    r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))),
% 5.22/1.06    inference(resolution,[],[f9579,f896])).
% 5.22/1.06  fof(f896,plain,(
% 5.22/1.06    ( ! [X28] : (~r1_tarski(X28,k4_xboole_0(sK0,sK2)) | r1_tarski(X28,k4_xboole_0(sK0,sK1))) )),
% 5.22/1.06    inference(subsumption_resolution,[],[f891,f892])).
% 5.22/1.06  fof(f891,plain,(
% 5.22/1.06    ( ! [X28] : (r1_tarski(X28,k4_xboole_0(sK0,sK1)) | ~r1_tarski(X28,k4_xboole_0(sK0,sK2)) | r1_tarski(sK1,sK2)) )),
% 5.22/1.06    inference(backward_demodulation,[],[f883,f881])).
% 5.22/1.06  fof(f883,plain,(
% 5.22/1.06    ( ! [X28] : (~r1_tarski(X28,k4_xboole_0(sK0,sK2)) | r1_tarski(X28,k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) )),
% 5.22/1.06    inference(backward_demodulation,[],[f296,f880])).
% 5.22/1.06  fof(f296,plain,(
% 5.22/1.06    ( ! [X28] : (~r1_tarski(X28,k3_subset_1(sK0,sK2)) | r1_tarski(X28,k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) )),
% 5.22/1.06    inference(resolution,[],[f75,f39])).
% 5.22/1.06  fof(f39,plain,(
% 5.22/1.06    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 5.22/1.06    inference(cnf_transformation,[],[f24])).
% 5.22/1.06  fof(f75,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f38])).
% 5.22/1.06  fof(f38,plain,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 5.22/1.06    inference(flattening,[],[f37])).
% 5.22/1.06  fof(f37,plain,(
% 5.22/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.22/1.06    inference(ennf_transformation,[],[f7])).
% 5.22/1.06  fof(f7,axiom,(
% 5.22/1.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 5.22/1.06  fof(f9579,plain,(
% 5.22/1.06    ( ! [X59] : (r1_tarski(k4_xboole_0(sK1,X59),k4_xboole_0(sK0,X59))) )),
% 5.22/1.06    inference(resolution,[],[f598,f5308])).
% 5.22/1.06  fof(f5308,plain,(
% 5.22/1.06    ( ! [X10] : (r1_tarski(sK1,k2_xboole_0(X10,sK0))) )),
% 5.22/1.06    inference(superposition,[],[f5270,f50])).
% 5.22/1.06  fof(f5270,plain,(
% 5.22/1.06    ( ! [X20] : (r1_tarski(sK1,k2_xboole_0(sK0,X20))) )),
% 5.22/1.06    inference(superposition,[],[f85,f3805])).
% 5.22/1.06  fof(f3805,plain,(
% 5.22/1.06    ( ! [X30] : (k2_xboole_0(sK0,X30) = k2_xboole_0(k2_xboole_0(sK0,X30),sK1)) )),
% 5.22/1.06    inference(forward_demodulation,[],[f3753,f45])).
% 5.22/1.06  fof(f3753,plain,(
% 5.22/1.06    ( ! [X30] : (k2_xboole_0(k2_xboole_0(sK0,X30),sK1) = k2_xboole_0(k2_xboole_0(sK0,X30),k1_xboole_0)) )),
% 5.22/1.06    inference(superposition,[],[f51,f3665])).
% 5.22/1.06  fof(f3665,plain,(
% 5.22/1.06    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,X7))) )),
% 5.22/1.06    inference(resolution,[],[f3657,f181])).
% 5.22/1.06  fof(f3657,plain,(
% 5.22/1.06    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK0,X0)),k1_xboole_0)) )),
% 5.22/1.06    inference(resolution,[],[f3066,f48])).
% 5.22/1.06  fof(f3066,plain,(
% 5.22/1.06    ( ! [X17] : (~r1_tarski(sK0,X17) | r1_tarski(k4_xboole_0(sK1,X17),k1_xboole_0)) )),
% 5.22/1.06    inference(superposition,[],[f70,f3022])).
% 5.22/1.06  fof(f3022,plain,(
% 5.22/1.06    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 5.22/1.06    inference(resolution,[],[f1923,f106])).
% 5.22/1.06  fof(f106,plain,(
% 5.22/1.06    r1_tarski(sK1,sK0)),
% 5.22/1.06    inference(resolution,[],[f104,f78])).
% 5.22/1.06  fof(f78,plain,(
% 5.22/1.06    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 5.22/1.06    inference(equality_resolution,[],[f65])).
% 5.22/1.06  fof(f65,plain,(
% 5.22/1.06    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 5.22/1.06    inference(cnf_transformation,[],[f18])).
% 5.22/1.06  fof(f18,axiom,(
% 5.22/1.06    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 5.22/1.06  fof(f104,plain,(
% 5.22/1.06    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 5.22/1.06    inference(subsumption_resolution,[],[f101,f43])).
% 5.22/1.06  fof(f43,plain,(
% 5.22/1.06    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 5.22/1.06    inference(cnf_transformation,[],[f21])).
% 5.22/1.06  fof(f21,axiom,(
% 5.22/1.06    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 5.22/1.06  fof(f101,plain,(
% 5.22/1.06    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 5.22/1.06    inference(resolution,[],[f55,f42])).
% 5.22/1.06  fof(f55,plain,(
% 5.22/1.06    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 5.22/1.06    inference(cnf_transformation,[],[f25])).
% 5.22/1.06  fof(f25,plain,(
% 5.22/1.06    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 5.22/1.06    inference(ennf_transformation,[],[f19])).
% 5.22/1.06  fof(f19,axiom,(
% 5.22/1.06    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 5.22/1.06  fof(f85,plain,(
% 5.22/1.06    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 5.22/1.06    inference(superposition,[],[f48,f50])).
% 5.22/1.06  fof(f598,plain,(
% 5.22/1.06    ( ! [X10,X8,X9] : (~r1_tarski(X10,k2_xboole_0(X8,X9)) | r1_tarski(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8))) )),
% 5.22/1.06    inference(superposition,[],[f71,f51])).
% 5.22/1.06  fof(f9746,plain,(
% 5.22/1.06    ( ! [X10] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),X10)) )),
% 5.22/1.06    inference(resolution,[],[f9734,f179])).
% 5.22/1.06  fof(f179,plain,(
% 5.22/1.06    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1) )),
% 5.22/1.06    inference(resolution,[],[f60,f49])).
% 5.22/1.06  fof(f51,plain,(
% 5.22/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.22/1.06    inference(cnf_transformation,[],[f12])).
% 5.22/1.06  fof(f12,axiom,(
% 5.22/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.22/1.06  fof(f48,plain,(
% 5.22/1.06    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.22/1.06    inference(cnf_transformation,[],[f15])).
% 5.22/1.06  fof(f15,axiom,(
% 5.22/1.06    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.22/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 5.22/1.06  % SZS output end Proof for theBenchmark
% 5.22/1.06  % (3970)------------------------------
% 5.22/1.06  % (3970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.06  % (3970)Termination reason: Refutation
% 5.22/1.06  
% 5.22/1.06  % (3970)Memory used [KB]: 10746
% 5.22/1.06  % (3970)Time elapsed: 0.637 s
% 5.22/1.06  % (3970)------------------------------
% 5.22/1.06  % (3970)------------------------------
% 5.22/1.06  % (3963)Success in time 0.696 s
%------------------------------------------------------------------------------
