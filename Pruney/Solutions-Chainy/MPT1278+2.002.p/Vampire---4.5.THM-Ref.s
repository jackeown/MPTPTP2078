%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 280 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  252 ( 877 expanded)
%              Number of equality atoms :   58 ( 190 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

% (19029)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

% (19031)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

fof(f160,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f153,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(backward_demodulation,[],[f68,f87])).

fof(f87,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f86,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f86,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f83,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

% (19008)Refutation not found, incomplete strategy% (19008)------------------------------
% (19008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19008)Termination reason: Refutation not found, incomplete strategy

% (19008)Memory used [KB]: 10746
% (19008)Time elapsed: 0.126 s
% (19008)------------------------------
% (19008)------------------------------
fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f68,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f153,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f70,f152])).

fof(f152,plain,(
    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f151,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f151,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f141,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f141,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f140,f136])).

fof(f136,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f115,f135])).

fof(f135,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f111,f134])).

fof(f134,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f133,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f132,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f129,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f129,plain,(
    v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f128,f87])).

fof(f128,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f125,f45])).

fof(f125,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f123,f79])).

fof(f79,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f78,f45])).

fof(f78,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_xboole_0,sK0) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f74,f42])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f123,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

% (19021)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f111,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f109,f66])).

fof(f109,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f108,f107])).

fof(f107,plain,(
    v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f106,f87])).

fof(f106,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,(
    v3_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f80,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v3_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ v3_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

% (19021)Refutation not found, incomplete strategy% (19021)------------------------------
% (19021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19021)Termination reason: Refutation not found, incomplete strategy

% (19021)Memory used [KB]: 6140
% (19021)Time elapsed: 0.002 s
% (19021)------------------------------
% (19021)------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f115,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f114,f37])).

% (19006)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f114,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f110,f60])).

fof(f110,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f108,f105])).

fof(f105,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f103,f37])).

fof(f103,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f102,f39])).

fof(f39,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f140,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f139,f42])).

fof(f139,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f127,f50])).

fof(f127,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f124,f37])).

fof(f124,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f123,f38])).

fof(f38,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f62,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:12:56 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.51  % (19009)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (19011)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19007)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (19028)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (19020)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (19012)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (19015)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (19015)Refutation not found, incomplete strategy% (19015)------------------------------
% 0.21/0.52  % (19015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19015)Memory used [KB]: 10618
% 0.21/0.52  % (19015)Time elapsed: 0.120 s
% 0.21/0.52  % (19015)------------------------------
% 0.21/0.52  % (19015)------------------------------
% 0.21/0.52  % (19028)Refutation not found, incomplete strategy% (19028)------------------------------
% 0.21/0.52  % (19028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19028)Memory used [KB]: 10746
% 0.21/0.52  % (19028)Time elapsed: 0.079 s
% 0.21/0.52  % (19028)------------------------------
% 0.21/0.52  % (19028)------------------------------
% 0.21/0.53  % (19034)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (19008)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (19030)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (19027)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (19012)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f160,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  % (19029)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  % (19031)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f19])).
% 0.21/0.53  fof(f19,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(forward_demodulation,[],[f153,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f68,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1) )),
% 0.21/0.53    inference(forward_demodulation,[],[f86,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f83,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 0.21/0.53    inference(resolution,[],[f65,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f61,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f59,f58])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  % (19008)Refutation not found, incomplete strategy% (19008)------------------------------
% 0.21/0.53  % (19008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19008)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19008)Memory used [KB]: 10746
% 0.21/0.53  % (19008)Time elapsed: 0.126 s
% 0.21/0.53  % (19008)------------------------------
% 0.21/0.53  % (19008)------------------------------
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 0.21/0.53    inference(resolution,[],[f62,f45])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f70,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f151,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f141,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f140,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f115,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f111,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f48,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f129,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f128,f87])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f45])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f123,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v3_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f78,f45])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.53    inference(resolution,[],[f75,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f42])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f56,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_pre_topc(X0,sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f55,f42])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  % (19021)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f66])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f108,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    v1_tops_1(u1_struct_0(sK0),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f87])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f104,f45])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(resolution,[],[f102,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    v3_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f45])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(resolution,[],[f77,f43])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_1(X0,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f42])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v3_tops_1(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f57,f41])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_tops_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.53    inference(resolution,[],[f51,f42])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f53,f42])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  % (19021)Refutation not found, incomplete strategy% (19021)------------------------------
% 0.21/0.53  % (19021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19021)Memory used [KB]: 6140
% 0.21/0.53  % (19021)Time elapsed: 0.002 s
% 0.21/0.53  % (19021)------------------------------
% 0.21/0.53  % (19021)------------------------------
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f114,f37])).
% 0.21/0.53  % (19006)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f110,f60])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(resolution,[],[f108,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f37])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f102,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v3_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f42])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(resolution,[],[f127,f50])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f124,f37])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f123,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v3_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(resolution,[],[f62,f37])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19012)------------------------------
% 0.21/0.53  % (19012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19006)Refutation not found, incomplete strategy% (19006)------------------------------
% 0.21/0.53  % (19006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19006)Memory used [KB]: 1663
% 0.21/0.53  % (19006)Time elapsed: 0.124 s
% 0.21/0.53  % (19006)------------------------------
% 0.21/0.53  % (19006)------------------------------
% 0.21/0.53  % (19012)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19012)Memory used [KB]: 6268
% 0.21/0.53  % (19012)Time elapsed: 0.092 s
% 0.21/0.53  % (19012)------------------------------
% 0.21/0.53  % (19012)------------------------------
% 0.21/0.54  % (19005)Success in time 0.173 s
%------------------------------------------------------------------------------
