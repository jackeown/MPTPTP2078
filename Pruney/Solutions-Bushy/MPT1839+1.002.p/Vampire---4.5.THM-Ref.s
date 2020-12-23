%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1839+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 314 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   27
%              Number of atoms          :  193 ( 801 expanded)
%              Number of equality atoms :   27 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(resolution,[],[f535,f30])).

fof(f30,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f535,plain,(
    ! [X1] : v1_xboole_0(k3_xboole_0(X1,sK1)) ),
    inference(resolution,[],[f529,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f529,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f524,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f524,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f520,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f519,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f519,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f515,f31])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f515,plain,
    ( v1_xboole_0(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f384,f401])).

fof(f401,plain,(
    m1_subset_1(sK2(sK0),sK1) ),
    inference(backward_demodulation,[],[f128,f386])).

fof(f386,plain,(
    sK2(sK0) = sK3(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f250,f139])).

fof(f139,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f136,plain,(
    r1_tarski(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),sK0) ),
    inference(resolution,[],[f133,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,(
    m1_subset_1(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f131,f132])).

fof(f132,plain,(
    k1_tarski(sK3(k3_xboole_0(sK0,sK1))) = k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f130,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f130,plain,
    ( v1_xboole_0(sK0)
    | k1_tarski(sK3(k3_xboole_0(sK0,sK1))) = k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f127,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f127,plain,(
    m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f126,f39])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
      | m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
      | m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f119,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f119,plain,(
    r2_hidden(sK3(k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f116,f47])).

fof(f116,plain,(
    r1_tarski(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f101,f49])).

fof(f101,plain,(
    m1_subset_1(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f99,f30])).

fof(f99,plain,
    ( m1_subset_1(k1_tarski(sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,sK1)))
    | v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f94,f86])).

fof(f86,plain,(
    k6_domain_1(k3_xboole_0(sK0,sK1),sK3(k3_xboole_0(sK0,sK1))) = k1_tarski(sK3(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,sK3(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f45,f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f131,plain,(
    m1_subset_1(k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f129,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k6_domain_1(sK0,sK3(k3_xboole_0(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f127,f45])).

fof(f250,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | sK2(sK0) = X4 ) ),
    inference(superposition,[],[f62,f245])).

fof(f245,plain,(
    sK0 = k1_tarski(sK2(sK0)) ),
    inference(forward_demodulation,[],[f244,f70])).

fof(f70,plain,(
    sK0 = k6_domain_1(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f69,f32])).

fof(f69,plain,
    ( sK0 = k6_domain_1(sK0,sK2(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f244,plain,(
    k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f243,f32])).

fof(f243,plain,
    ( k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f83,f33])).

fof(f83,plain,(
    ! [X5] :
      ( ~ v1_zfmisc_1(X5)
      | k6_domain_1(X5,sK2(X5)) = k1_tarski(sK2(X5))
      | v1_xboole_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X5] :
      ( v1_xboole_0(X5)
      | k6_domain_1(X5,sK2(X5)) = k1_tarski(sK2(X5))
      | v1_xboole_0(X5)
      | ~ v1_zfmisc_1(X5) ) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f128,plain,(
    m1_subset_1(sK3(k3_xboole_0(sK0,sK1)),sK1) ),
    inference(resolution,[],[f126,f53])).

fof(f384,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0),X0)
      | v1_xboole_0(X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f248,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f248,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(sK0),X2)
      | r1_tarski(sK0,X2) ) ),
    inference(superposition,[],[f46,f245])).

%------------------------------------------------------------------------------
