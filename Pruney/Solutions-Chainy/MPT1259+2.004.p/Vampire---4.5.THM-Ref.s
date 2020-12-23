%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:30 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   88 (1195 expanded)
%              Number of leaves         :   13 ( 233 expanded)
%              Depth                    :   28
%              Number of atoms          :  211 (3304 expanded)
%              Number of equality atoms :   50 ( 806 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(subsumption_resolution,[],[f466,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

fof(f466,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f465,f204])).

fof(f204,plain,(
    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f196,f203])).

fof(f203,plain,(
    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f202,f47])).

fof(f202,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f199,f192])).

fof(f192,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f191,f107])).

fof(f107,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f106,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f94])).

fof(f94,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f55,f78])).

fof(f78,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f103,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f48,f86])).

fof(f86,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f85,f78])).

fof(f85,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f75,f47])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f191,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f55,f119])).

fof(f119,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f107,f54])).

fof(f199,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f48,f127])).

fof(f127,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f126,f119])).

fof(f126,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f116,f47])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f107,f49])).

fof(f196,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f195,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f194,f47])).

fof(f194,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f50,f125])).

fof(f125,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f124,f46])).

fof(f124,plain,
    ( ~ v2_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f115,f47])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f107,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f465,plain,
    ( ~ v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f464,f203])).

fof(f464,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f429,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f429,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f425,f45])).

fof(f45,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f425,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f390,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f390,plain,(
    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f60,f325])).

fof(f325,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f222,f217])).

fof(f217,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
    inference(resolution,[],[f203,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f222,plain,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f221,f82])).

fof(f82,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f81,f46])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f73,f47])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

fof(f221,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f213,f47])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f203,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (31214)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (31212)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (31237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (31215)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (31227)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (31222)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (31237)Refutation not found, incomplete strategy% (31237)------------------------------
% 0.21/0.57  % (31237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (31220)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (31232)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.59  % (31209)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (31211)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.59  % (31210)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.59  % (31210)Refutation not found, incomplete strategy% (31210)------------------------------
% 0.21/0.59  % (31210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (31210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (31210)Memory used [KB]: 1663
% 0.21/0.59  % (31210)Time elapsed: 0.168 s
% 0.21/0.59  % (31210)------------------------------
% 0.21/0.59  % (31210)------------------------------
% 0.21/0.59  % (31213)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (31224)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.59  % (31237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (31237)Memory used [KB]: 10746
% 0.21/0.59  % (31237)Time elapsed: 0.148 s
% 0.21/0.59  % (31237)------------------------------
% 0.21/0.59  % (31237)------------------------------
% 0.21/0.60  % (31225)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.61  % (31217)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.61  % (31216)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.62  % (31230)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.62  % (31233)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.62  % (31229)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.62  % (31236)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.63  % (31238)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.63  % (31238)Refutation not found, incomplete strategy% (31238)------------------------------
% 0.21/0.63  % (31238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (31238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.63  
% 0.21/0.63  % (31238)Memory used [KB]: 1663
% 0.21/0.63  % (31238)Time elapsed: 0.002 s
% 0.21/0.63  % (31238)------------------------------
% 0.21/0.63  % (31238)------------------------------
% 0.21/0.63  % (31225)Refutation not found, incomplete strategy% (31225)------------------------------
% 0.21/0.63  % (31225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (31225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.63  
% 0.21/0.63  % (31225)Memory used [KB]: 10618
% 0.21/0.63  % (31225)Time elapsed: 0.197 s
% 0.21/0.63  % (31225)------------------------------
% 0.21/0.63  % (31225)------------------------------
% 0.21/0.63  % (31228)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.63  % (31223)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.63  % (31234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.63  % (31231)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.63  % (31221)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.99/0.64  % (31235)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.99/0.64  % (31218)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.99/0.64  % (31226)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.99/0.65  % (31219)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.99/0.65  % (31219)Refutation not found, incomplete strategy% (31219)------------------------------
% 1.99/0.65  % (31219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (31219)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.65  
% 1.99/0.65  % (31219)Memory used [KB]: 10746
% 1.99/0.65  % (31219)Time elapsed: 0.229 s
% 1.99/0.65  % (31219)------------------------------
% 1.99/0.65  % (31219)------------------------------
% 2.26/0.66  % (31236)Refutation found. Thanks to Tanya!
% 2.26/0.66  % SZS status Theorem for theBenchmark
% 2.26/0.66  % SZS output start Proof for theBenchmark
% 2.26/0.66  fof(f467,plain,(
% 2.26/0.66    $false),
% 2.26/0.66    inference(subsumption_resolution,[],[f466,f47])).
% 2.26/0.66  fof(f47,plain,(
% 2.26/0.66    l1_pre_topc(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f24,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f23])).
% 2.26/0.66  fof(f23,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f22])).
% 2.26/0.66  fof(f22,negated_conjecture,(
% 2.26/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.26/0.66    inference(negated_conjecture,[],[f21])).
% 2.26/0.66  fof(f21,conjecture,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).
% 2.26/0.66  fof(f466,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f465,f204])).
% 2.26/0.66  fof(f204,plain,(
% 2.26/0.66    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f196,f203])).
% 2.26/0.66  fof(f203,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f202,f47])).
% 2.26/0.66  fof(f202,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f199,f192])).
% 2.26/0.66  fof(f192,plain,(
% 2.26/0.66    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f191,f107])).
% 2.26/0.66  fof(f107,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f106,f47])).
% 2.26/0.66  fof(f106,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f103,f94])).
% 2.26/0.66  fof(f94,plain,(
% 2.26/0.66    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f93,f44])).
% 2.26/0.66  fof(f44,plain,(
% 2.26/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f93,plain,(
% 2.26/0.66    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(superposition,[],[f55,f78])).
% 2.26/0.66  fof(f78,plain,(
% 2.26/0.66    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 2.26/0.66    inference(resolution,[],[f44,f54])).
% 2.26/0.66  fof(f54,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f35])).
% 2.26/0.66  fof(f35,plain,(
% 2.26/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f8])).
% 2.26/0.66  fof(f8,axiom,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.26/0.66  fof(f55,plain,(
% 2.26/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f36])).
% 2.26/0.66  fof(f36,plain,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f9])).
% 2.26/0.66  fof(f9,axiom,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.26/0.66  fof(f103,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(superposition,[],[f48,f86])).
% 2.26/0.66  fof(f86,plain,(
% 2.26/0.66    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.26/0.66    inference(backward_demodulation,[],[f85,f78])).
% 2.26/0.66  fof(f85,plain,(
% 2.26/0.66    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.26/0.66    inference(subsumption_resolution,[],[f75,f47])).
% 2.26/0.66  fof(f75,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.26/0.66    inference(resolution,[],[f44,f49])).
% 2.26/0.66  fof(f49,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f27])).
% 2.26/0.66  fof(f27,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f18])).
% 2.26/0.66  fof(f18,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 2.26/0.66  fof(f48,plain,(
% 2.26/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f26])).
% 2.26/0.66  fof(f26,plain,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f25])).
% 2.26/0.66  fof(f25,plain,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f14])).
% 2.26/0.66  fof(f14,axiom,(
% 2.26/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.26/0.66  fof(f191,plain,(
% 2.26/0.66    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(superposition,[],[f55,f119])).
% 2.26/0.66  fof(f119,plain,(
% 2.26/0.66    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),
% 2.26/0.66    inference(resolution,[],[f107,f54])).
% 2.26/0.66  fof(f199,plain,(
% 2.26/0.66    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(superposition,[],[f48,f127])).
% 2.26/0.66  fof(f127,plain,(
% 2.26/0.66    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(backward_demodulation,[],[f126,f119])).
% 2.26/0.66  fof(f126,plain,(
% 2.26/0.66    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f116,f47])).
% 2.26/0.66  fof(f116,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0) | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(resolution,[],[f107,f49])).
% 2.26/0.66  fof(f196,plain,(
% 2.26/0.66    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f195,f46])).
% 2.26/0.66  fof(f46,plain,(
% 2.26/0.66    v2_pre_topc(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f195,plain,(
% 2.26/0.66    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f194,f47])).
% 2.26/0.66  fof(f194,plain,(
% 2.26/0.66    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 2.26/0.66    inference(superposition,[],[f50,f125])).
% 2.26/0.66  fof(f125,plain,(
% 2.26/0.66    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f124,f46])).
% 2.26/0.66  fof(f124,plain,(
% 2.26/0.66    ~v2_pre_topc(sK0) | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f115,f47])).
% 2.26/0.66  fof(f115,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(resolution,[],[f107,f51])).
% 2.26/0.66  fof(f51,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f31])).
% 2.26/0.66  fof(f31,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f30])).
% 2.26/0.66  fof(f30,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f16])).
% 2.26/0.66  fof(f16,axiom,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).
% 2.26/0.66  fof(f50,plain,(
% 2.26/0.66    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f29])).
% 2.26/0.66  fof(f29,plain,(
% 2.26/0.66    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f28])).
% 2.26/0.66  fof(f28,plain,(
% 2.26/0.66    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f15])).
% 2.26/0.66  fof(f15,axiom,(
% 2.26/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.26/0.66  fof(f465,plain,(
% 2.26/0.66    ~v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(subsumption_resolution,[],[f464,f203])).
% 2.26/0.66  fof(f464,plain,(
% 2.26/0.66    ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~l1_pre_topc(sK0)),
% 2.26/0.66    inference(resolution,[],[f429,f56])).
% 2.26/0.66  fof(f56,plain,(
% 2.26/0.66    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f38,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f37])).
% 2.26/0.66  fof(f37,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f19])).
% 2.26/0.66  fof(f19,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.26/0.66  fof(f429,plain,(
% 2.26/0.66    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f425,f45])).
% 2.26/0.66  fof(f45,plain,(
% 2.26/0.66    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(cnf_transformation,[],[f24])).
% 2.26/0.66  fof(f425,plain,(
% 2.26/0.66    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(resolution,[],[f390,f66])).
% 2.26/0.66  fof(f66,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.26/0.66    inference(cnf_transformation,[],[f2])).
% 2.26/0.66  fof(f2,axiom,(
% 2.26/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.26/0.66  fof(f390,plain,(
% 2.26/0.66    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(trivial_inequality_removal,[],[f389])).
% 2.26/0.66  fof(f389,plain,(
% 2.26/0.66    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(superposition,[],[f60,f325])).
% 2.26/0.66  fof(f325,plain,(
% 2.26/0.66    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(superposition,[],[f222,f217])).
% 2.26/0.66  fof(f217,plain,(
% 2.26/0.66    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) )),
% 2.26/0.66    inference(resolution,[],[f203,f68])).
% 2.26/0.66  fof(f68,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f43])).
% 2.26/0.66  fof(f43,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f11])).
% 2.26/0.66  fof(f11,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.26/0.66  fof(f222,plain,(
% 2.26/0.66    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(forward_demodulation,[],[f221,f82])).
% 2.26/0.66  fof(f82,plain,(
% 2.26/0.66    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f81,f46])).
% 2.26/0.66  fof(f81,plain,(
% 2.26/0.66    ~v2_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(subsumption_resolution,[],[f73,f47])).
% 2.26/0.66  fof(f73,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.26/0.66    inference(resolution,[],[f44,f52])).
% 2.26/0.66  fof(f52,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f33])).
% 2.26/0.66  fof(f33,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.26/0.66    inference(flattening,[],[f32])).
% 2.26/0.66  fof(f32,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f17])).
% 2.26/0.66  fof(f17,axiom,(
% 2.26/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).
% 2.26/0.66  fof(f221,plain,(
% 2.26/0.66    k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(subsumption_resolution,[],[f213,f47])).
% 2.26/0.66  fof(f213,plain,(
% 2.26/0.66    ~l1_pre_topc(sK0) | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.26/0.66    inference(resolution,[],[f203,f58])).
% 2.26/0.66  fof(f58,plain,(
% 2.26/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.26/0.66    inference(cnf_transformation,[],[f41])).
% 2.26/0.66  fof(f41,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f20])).
% 2.26/0.66  fof(f20,axiom,(
% 2.26/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.26/0.66  fof(f60,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f3])).
% 2.26/0.66  fof(f3,axiom,(
% 2.26/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.26/0.66  % SZS output end Proof for theBenchmark
% 2.26/0.66  % (31236)------------------------------
% 2.26/0.66  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (31236)Termination reason: Refutation
% 2.26/0.66  
% 2.26/0.66  % (31236)Memory used [KB]: 6524
% 2.26/0.66  % (31236)Time elapsed: 0.230 s
% 2.26/0.66  % (31236)------------------------------
% 2.26/0.66  % (31236)------------------------------
% 2.26/0.66  % (31208)Success in time 0.297 s
%------------------------------------------------------------------------------
