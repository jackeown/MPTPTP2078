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
% DateTime   : Thu Dec  3 13:12:40 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 808 expanded)
%              Number of leaves         :   14 ( 167 expanded)
%              Depth                    :   21
%              Number of atoms          :  234 (2075 expanded)
%              Number of equality atoms :   34 ( 194 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1272,plain,(
    $false ),
    inference(global_subsumption,[],[f358,f620,f1271])).

fof(f1271,plain,(
    r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1270,f219])).

fof(f219,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f208,f161])).

fof(f161,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f113,f78])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f44,f77])).

fof(f77,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f73,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6))) ) ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f106,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6))) ) ),
    inference(superposition,[],[f66,f77])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f208,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f142,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f142,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f110,f81])).

fof(f81,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f110,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(superposition,[],[f60,f77])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1270,plain,(
    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f1252,f164])).

fof(f164,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f137,f163])).

fof(f163,plain,(
    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f162,f82])).

fof(f82,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f78,f54])).

fof(f162,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f113,f81])).

fof(f137,plain,(
    r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f114,f81])).

fof(f114,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X7),X7) ) ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | r1_tarski(k1_tops_1(sK0,X7),X7) ) ),
    inference(superposition,[],[f69,f77])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1252,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f396,f81])).

fof(f396,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) ) ),
    inference(forward_demodulation,[],[f381,f292])).

fof(f292,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f291,f176])).

fof(f176,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f141,f55])).

fof(f141,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f110,f78])).

fof(f291,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f290,f77])).

fof(f290,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f289,f47])).

fof(f289,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f165,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f165,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(resolution,[],[f141,f92])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f91,f77])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f90,f77])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f76,plain,(
    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f75,f47])).

fof(f75,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f45,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f176,f111])).

fof(f111,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4)) ) ),
    inference(superposition,[],[f61,f77])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f620,plain,(
    k2_struct_0(sK0) != k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f148,f219])).

fof(f148,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f147,f79])).

fof(f79,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f46,f77])).

fof(f46,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f147,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f108,f81])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f48,f77])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f358,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f228,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f228,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f206,f219])).

fof(f206,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f142,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (19300)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (19308)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (19298)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (19288)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (19299)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (19297)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (19291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (19311)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (19310)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (19302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (19292)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (19313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (19304)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (19290)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (19294)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (19309)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (19295)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (19289)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (19305)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (19293)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (19307)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (19296)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (19303)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (19306)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (19312)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (19301)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.99/0.62  % (19297)Refutation not found, incomplete strategy% (19297)------------------------------
% 1.99/0.62  % (19297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.62  % (19297)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.62  
% 1.99/0.62  % (19297)Memory used [KB]: 6140
% 1.99/0.62  % (19297)Time elapsed: 0.208 s
% 1.99/0.62  % (19297)------------------------------
% 1.99/0.62  % (19297)------------------------------
% 2.12/0.63  % (19293)Refutation found. Thanks to Tanya!
% 2.12/0.63  % SZS status Theorem for theBenchmark
% 2.12/0.63  % SZS output start Proof for theBenchmark
% 2.12/0.63  fof(f1272,plain,(
% 2.12/0.63    $false),
% 2.12/0.63    inference(global_subsumption,[],[f358,f620,f1271])).
% 2.12/0.63  fof(f1271,plain,(
% 2.12/0.63    r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 2.12/0.63    inference(forward_demodulation,[],[f1270,f219])).
% 2.12/0.63  fof(f219,plain,(
% 2.12/0.63    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.12/0.63    inference(forward_demodulation,[],[f208,f161])).
% 2.12/0.63  fof(f161,plain,(
% 2.12/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.12/0.63    inference(resolution,[],[f113,f78])).
% 2.12/0.63  fof(f78,plain,(
% 2.12/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.12/0.63    inference(backward_demodulation,[],[f44,f77])).
% 2.12/0.63  fof(f77,plain,(
% 2.12/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.12/0.63    inference(resolution,[],[f73,f67])).
% 2.12/0.63  fof(f67,plain,(
% 2.12/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f39])).
% 2.12/0.63  fof(f39,plain,(
% 2.12/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.12/0.63    inference(ennf_transformation,[],[f9])).
% 2.12/0.63  fof(f9,axiom,(
% 2.12/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.12/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.12/0.63  fof(f73,plain,(
% 2.12/0.63    l1_struct_0(sK0)),
% 2.12/0.63    inference(resolution,[],[f47,f70])).
% 2.12/0.63  fof(f70,plain,(
% 2.12/0.63    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f43])).
% 2.12/0.63  fof(f43,plain,(
% 2.12/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.12/0.63    inference(ennf_transformation,[],[f11])).
% 2.12/0.63  fof(f11,axiom,(
% 2.12/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.12/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.12/0.63  fof(f47,plain,(
% 2.12/0.63    l1_pre_topc(sK0)),
% 2.12/0.63    inference(cnf_transformation,[],[f23])).
% 2.12/0.63  fof(f23,plain,(
% 2.12/0.63    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.12/0.63    inference(flattening,[],[f22])).
% 2.12/0.63  fof(f22,plain,(
% 2.12/0.63    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.12/0.63    inference(ennf_transformation,[],[f21])).
% 2.12/0.63  fof(f21,negated_conjecture,(
% 2.12/0.63    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.12/0.63    inference(negated_conjecture,[],[f20])).
% 2.12/0.64  fof(f20,conjecture,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 2.12/0.64  fof(f44,plain,(
% 2.12/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.64    inference(cnf_transformation,[],[f23])).
% 2.12/0.64  fof(f113,plain,(
% 2.12/0.64    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6)))) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f106,f47])).
% 2.12/0.64  fof(f106,plain,(
% 2.12/0.64    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6)))) )),
% 2.12/0.64    inference(superposition,[],[f66,f77])).
% 2.12/0.64  fof(f66,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f38])).
% 2.12/0.64  fof(f38,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f14])).
% 2.12/0.64  fof(f14,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.12/0.64  fof(f208,plain,(
% 2.12/0.64    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))),
% 2.12/0.64    inference(resolution,[],[f142,f54])).
% 2.12/0.64  fof(f54,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.12/0.64    inference(cnf_transformation,[],[f30])).
% 2.12/0.64  fof(f30,plain,(
% 2.12/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f5])).
% 2.12/0.64  fof(f5,axiom,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.12/0.64  fof(f142,plain,(
% 2.12/0.64    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.12/0.64    inference(resolution,[],[f110,f81])).
% 2.12/0.64  fof(f81,plain,(
% 2.12/0.64    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.12/0.64    inference(resolution,[],[f78,f55])).
% 2.12/0.64  fof(f55,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f31])).
% 2.12/0.64  fof(f31,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f4])).
% 2.12/0.64  fof(f4,axiom,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.12/0.64  fof(f110,plain,(
% 2.12/0.64    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f103,f47])).
% 2.12/0.64  fof(f103,plain,(
% 2.12/0.64    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.12/0.64    inference(superposition,[],[f60,f77])).
% 2.12/0.64  fof(f60,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f34])).
% 2.12/0.64  fof(f34,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f33])).
% 2.12/0.64  fof(f33,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f10])).
% 2.12/0.64  fof(f10,axiom,(
% 2.12/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.12/0.64  fof(f1270,plain,(
% 2.12/0.64    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.12/0.64    inference(subsumption_resolution,[],[f1252,f164])).
% 2.12/0.64  fof(f164,plain,(
% 2.12/0.64    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(backward_demodulation,[],[f137,f163])).
% 2.12/0.64  fof(f163,plain,(
% 2.12/0.64    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(forward_demodulation,[],[f162,f82])).
% 2.12/0.64  fof(f82,plain,(
% 2.12/0.64    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(resolution,[],[f78,f54])).
% 2.12/0.64  fof(f162,plain,(
% 2.12/0.64    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))),
% 2.12/0.64    inference(resolution,[],[f113,f81])).
% 2.12/0.64  fof(f137,plain,(
% 2.12/0.64    r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(resolution,[],[f114,f81])).
% 2.12/0.64  fof(f114,plain,(
% 2.12/0.64    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X7),X7)) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f107,f47])).
% 2.12/0.64  fof(f107,plain,(
% 2.12/0.64    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,X7),X7)) )),
% 2.12/0.64    inference(superposition,[],[f69,f77])).
% 2.12/0.64  fof(f69,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f42])).
% 2.12/0.64  fof(f42,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f18])).
% 2.12/0.64  fof(f18,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.12/0.64  fof(f1252,plain,(
% 2.12/0.64    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(resolution,[],[f396,f81])).
% 2.12/0.64  fof(f396,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f381,f292])).
% 2.12/0.64  fof(f292,plain,(
% 2.12/0.64    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.12/0.64    inference(subsumption_resolution,[],[f291,f176])).
% 2.12/0.64  fof(f176,plain,(
% 2.12/0.64    m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.12/0.64    inference(resolution,[],[f141,f55])).
% 2.12/0.64  fof(f141,plain,(
% 2.12/0.64    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.12/0.64    inference(resolution,[],[f110,f78])).
% 2.12/0.64  fof(f291,plain,(
% 2.12/0.64    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.12/0.64    inference(forward_demodulation,[],[f290,f77])).
% 2.12/0.64  fof(f290,plain,(
% 2.12/0.64    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.12/0.64    inference(subsumption_resolution,[],[f289,f47])).
% 2.12/0.64  fof(f289,plain,(
% 2.12/0.64    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(resolution,[],[f165,f49])).
% 2.12/0.64  fof(f49,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f24])).
% 2.12/0.64  fof(f24,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f15])).
% 2.12/0.64  fof(f15,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 2.12/0.64  fof(f165,plain,(
% 2.12/0.64    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.12/0.64    inference(resolution,[],[f141,f92])).
% 2.12/0.64  fof(f92,plain,(
% 2.12/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.12/0.64    inference(forward_demodulation,[],[f91,f77])).
% 2.12/0.64  fof(f91,plain,(
% 2.12/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.12/0.64    inference(forward_demodulation,[],[f90,f77])).
% 2.12/0.64  fof(f90,plain,(
% 2.12/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.12/0.64    inference(subsumption_resolution,[],[f89,f47])).
% 2.12/0.64  fof(f89,plain,(
% 2.12/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(resolution,[],[f76,f51])).
% 2.12/0.64  fof(f51,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f25])).
% 2.12/0.64  fof(f25,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f16])).
% 2.12/0.64  fof(f16,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 2.12/0.64  fof(f76,plain,(
% 2.12/0.64    v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 2.12/0.64    inference(subsumption_resolution,[],[f75,f47])).
% 2.12/0.64  fof(f75,plain,(
% 2.12/0.64    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(subsumption_resolution,[],[f74,f44])).
% 2.12/0.64  fof(f74,plain,(
% 2.12/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(resolution,[],[f45,f57])).
% 2.12/0.64  fof(f57,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f32])).
% 2.12/0.64  fof(f32,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f17])).
% 2.12/0.64  fof(f17,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).
% 2.12/0.64  fof(f45,plain,(
% 2.12/0.64    v3_tops_1(sK1,sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f23])).
% 2.12/0.64  fof(f381,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X0))) )),
% 2.12/0.64    inference(resolution,[],[f176,f111])).
% 2.12/0.64  fof(f111,plain,(
% 2.12/0.64    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4))) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f104,f47])).
% 2.12/0.64  fof(f104,plain,(
% 2.12/0.64    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4))) )),
% 2.12/0.64    inference(superposition,[],[f61,f77])).
% 2.12/0.64  fof(f61,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f36])).
% 2.12/0.64  fof(f36,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f35])).
% 2.12/0.64  fof(f35,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f13])).
% 2.12/0.64  fof(f13,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 2.12/0.64  fof(f620,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.12/0.64    inference(superposition,[],[f148,f219])).
% 2.12/0.64  fof(f148,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.12/0.64    inference(subsumption_resolution,[],[f147,f79])).
% 2.12/0.64  fof(f79,plain,(
% 2.12/0.64    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.12/0.64    inference(backward_demodulation,[],[f46,f77])).
% 2.12/0.64  fof(f46,plain,(
% 2.12/0.64    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f23])).
% 2.12/0.64  fof(f147,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.12/0.64    inference(resolution,[],[f108,f81])).
% 2.12/0.64  fof(f108,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f101,f47])).
% 2.12/0.64  fof(f101,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 2.12/0.64    inference(superposition,[],[f48,f77])).
% 2.12/0.64  fof(f48,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f24])).
% 2.12/0.64  fof(f358,plain,(
% 2.12/0.64    ~r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.12/0.64    inference(resolution,[],[f228,f65])).
% 2.12/0.64  fof(f65,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.12/0.64    inference(cnf_transformation,[],[f1])).
% 2.12/0.64  fof(f1,axiom,(
% 2.12/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.12/0.64  fof(f228,plain,(
% 2.12/0.64    r1_tarski(k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)),k2_struct_0(sK0))),
% 2.12/0.64    inference(backward_demodulation,[],[f206,f219])).
% 2.12/0.64  fof(f206,plain,(
% 2.12/0.64    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))),
% 2.12/0.64    inference(resolution,[],[f142,f59])).
% 2.12/0.64  fof(f59,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f8])).
% 2.12/0.64  fof(f8,axiom,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.12/0.64  % SZS output end Proof for theBenchmark
% 2.12/0.64  % (19293)------------------------------
% 2.12/0.64  % (19293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (19293)Termination reason: Refutation
% 2.12/0.64  
% 2.12/0.64  % (19293)Memory used [KB]: 7547
% 2.12/0.64  % (19293)Time elapsed: 0.225 s
% 2.12/0.64  % (19293)------------------------------
% 2.12/0.64  % (19293)------------------------------
% 2.12/0.64  % (19287)Success in time 0.283 s
%------------------------------------------------------------------------------
