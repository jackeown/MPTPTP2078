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
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   92 (1198 expanded)
%              Number of leaves         :   13 ( 272 expanded)
%              Depth                    :   22
%              Number of atoms          :  269 (5065 expanded)
%              Number of equality atoms :   49 ( 793 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(global_subsumption,[],[f396,f422])).

fof(f422,plain,(
    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f411,f294])).

fof(f294,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f235,f289])).

fof(f289,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f37,f38,f151,f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

% (4820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (4821)Refutation not found, incomplete strategy% (4821)------------------------------
% (4821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4821)Termination reason: Refutation not found, incomplete strategy

% (4821)Memory used [KB]: 10618
% (4821)Time elapsed: 0.150 s
% (4821)------------------------------
% (4821)------------------------------
% (4819)Termination reason: Refutation not found, incomplete strategy

% (4819)Memory used [KB]: 10746
% (4819)Time elapsed: 0.149 s
% (4819)------------------------------
% (4819)------------------------------
% (4837)Refutation not found, incomplete strategy% (4837)------------------------------
% (4837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4837)Termination reason: Refutation not found, incomplete strategy

% (4837)Memory used [KB]: 11001
% (4837)Time elapsed: 0.169 s
% (4837)------------------------------
% (4837)------------------------------
fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f151,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f40,f150,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f150,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f145,f125])).

fof(f125,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f76,f117,f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f117,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f40,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f50,f40,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f50,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f145,plain,(
    v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f39,f38,f40,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f235,plain,(
    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f207,f230])).

fof(f230,plain,(
    u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) = k5_tmap_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f207,plain,(
    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f189,f197])).

fof(f197,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f189,plain,(
    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,k1_xboole_0)),u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f160,f178,f41])).

fof(f41,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f178,plain,(
    l1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f38,f37,f39,f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f160,plain,(
    v1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f38,f37,f39,f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f411,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f236,f402])).

fof(f402,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f400,f48])).

fof(f400,plain,(
    r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f36,f395,f44])).

fof(f395,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f39,f38,f37,f36,f132,f394])).

fof(f394,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f47,f323])).

fof(f323,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f39,f38,f37,f36,f322])).

fof(f322,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f318,f295])).

fof(f295,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f230,f289])).

fof(f318,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) = k5_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f46,f296])).

fof(f296,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0)
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f34,f294])).

fof(f34,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f39,f129])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f236,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f210,f229])).

fof(f229,plain,(
    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f46])).

fof(f210,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f183,f196])).

fof(f196,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f45])).

fof(f183,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f159,f177,f41])).

fof(f177,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f53])).

fof(f159,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f51])).

fof(f396,plain,(
    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f395,f297])).

fof(f297,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f35,f294])).

fof(f35,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (4814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4813)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (4824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (4840)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (4815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (4832)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (4834)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (4812)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (4811)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4817)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (4826)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (4835)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (4841)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (4831)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (4813)Refutation not found, incomplete strategy% (4813)------------------------------
% 0.21/0.54  % (4813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4813)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4813)Memory used [KB]: 10746
% 0.21/0.54  % (4813)Time elapsed: 0.125 s
% 0.21/0.54  % (4813)------------------------------
% 0.21/0.54  % (4813)------------------------------
% 0.21/0.54  % (4818)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4838)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (4827)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (4836)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (4830)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (4829)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (4828)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (4828)Refutation not found, incomplete strategy% (4828)------------------------------
% 0.21/0.55  % (4828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4828)Memory used [KB]: 10618
% 0.21/0.55  % (4828)Time elapsed: 0.135 s
% 0.21/0.55  % (4828)------------------------------
% 0.21/0.55  % (4828)------------------------------
% 0.21/0.55  % (4825)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (4837)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (4822)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (4833)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (4822)Refutation not found, incomplete strategy% (4822)------------------------------
% 0.21/0.56  % (4822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4822)Memory used [KB]: 10618
% 0.21/0.56  % (4822)Time elapsed: 0.146 s
% 0.21/0.56  % (4822)------------------------------
% 0.21/0.56  % (4822)------------------------------
% 0.21/0.56  % (4819)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (4819)Refutation not found, incomplete strategy% (4819)------------------------------
% 0.21/0.56  % (4819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4823)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (4821)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (4833)Refutation not found, incomplete strategy% (4833)------------------------------
% 0.21/0.56  % (4833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4833)Memory used [KB]: 10746
% 0.21/0.56  % (4833)Time elapsed: 0.136 s
% 0.21/0.56  % (4833)------------------------------
% 0.21/0.56  % (4833)------------------------------
% 0.21/0.57  % (4835)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f423,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(global_subsumption,[],[f396,f422])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f411,f294])).
% 0.21/0.57  fof(f294,plain,(
% 0.21/0.57    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f235,f289])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    u1_pre_topc(sK0) = k5_tmap_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f39,f37,f38,f151,f40,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  % (4820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (4821)Refutation not found, incomplete strategy% (4821)------------------------------
% 0.21/0.57  % (4821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (4821)Memory used [KB]: 10618
% 0.21/0.57  % (4821)Time elapsed: 0.150 s
% 0.21/0.57  % (4821)------------------------------
% 0.21/0.57  % (4821)------------------------------
% 1.62/0.57  % (4819)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (4819)Memory used [KB]: 10746
% 1.62/0.57  % (4819)Time elapsed: 0.149 s
% 1.62/0.57  % (4819)------------------------------
% 1.62/0.57  % (4819)------------------------------
% 1.62/0.58  % (4837)Refutation not found, incomplete strategy% (4837)------------------------------
% 1.62/0.58  % (4837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (4837)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (4837)Memory used [KB]: 11001
% 1.62/0.58  % (4837)Time elapsed: 0.169 s
% 1.62/0.58  % (4837)------------------------------
% 1.62/0.58  % (4837)------------------------------
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.58    inference(flattening,[],[f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.62/0.58  fof(f151,plain,(
% 1.62/0.58    r2_hidden(k1_xboole_0,u1_pre_topc(sK0))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f39,f40,f150,f44])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f21])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.62/0.58  fof(f150,plain,(
% 1.62/0.58    v3_pre_topc(k1_xboole_0,sK0)),
% 1.62/0.58    inference(forward_demodulation,[],[f145,f125])).
% 1.62/0.58  fof(f125,plain,(
% 1.62/0.58    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f76,f117,f57])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.58  fof(f117,plain,(
% 1.62/0.58    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f39,f40,f42])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f20])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.62/0.58  fof(f76,plain,(
% 1.62/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f71,f59])).
% 1.62/0.58  fof(f59,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.58  fof(f71,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f50,f40,f62])).
% 1.62/0.58  fof(f62,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.62/0.58  fof(f145,plain,(
% 1.62/0.58    v3_pre_topc(k1_tops_1(sK0,k1_xboole_0),sK0)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f39,f38,f40,f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    v2_pre_topc(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.62/0.58    inference(flattening,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,negated_conjecture,(
% 1.62/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.62/0.58    inference(negated_conjecture,[],[f14])).
% 1.62/0.58  fof(f14,conjecture,(
% 1.62/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    ~v2_struct_0(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    l1_pre_topc(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f235,plain,(
% 1.62/0.58    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,k1_xboole_0))),
% 1.62/0.58    inference(backward_demodulation,[],[f207,f230])).
% 1.62/0.58  fof(f230,plain,(
% 1.62/0.58    u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) = k5_tmap_1(sK0,k1_xboole_0)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f46])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.58    inference(flattening,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,axiom,(
% 1.62/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.62/0.58  fof(f207,plain,(
% 1.62/0.58    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)))),
% 1.62/0.58    inference(backward_demodulation,[],[f189,f197])).
% 1.62/0.58  fof(f197,plain,(
% 1.62/0.58    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,k1_xboole_0))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f45])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f23])).
% 1.62/0.58  fof(f189,plain,(
% 1.62/0.58    k6_tmap_1(sK0,k1_xboole_0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,k1_xboole_0)),u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f160,f178,f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f18])).
% 1.62/0.58  fof(f18,plain,(
% 1.62/0.58    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.62/0.58  fof(f178,plain,(
% 1.62/0.58    l1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f38,f37,f39,f40,f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.58    inference(flattening,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.62/0.58  fof(f160,plain,(
% 1.62/0.58    v1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f38,f37,f39,f40,f51])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f411,plain,(
% 1.62/0.58    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 1.62/0.58    inference(backward_demodulation,[],[f236,f402])).
% 1.62/0.58  fof(f402,plain,(
% 1.62/0.58    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f400,f48])).
% 1.62/0.58  fof(f400,plain,(
% 1.62/0.58    r2_hidden(sK1,u1_pre_topc(sK0))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f39,f36,f395,f44])).
% 1.62/0.58  fof(f395,plain,(
% 1.62/0.58    v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(global_subsumption,[],[f39,f38,f37,f36,f132,f394])).
% 1.62/0.58  fof(f394,plain,(
% 1.62/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f393])).
% 1.62/0.58  fof(f393,plain,(
% 1.62/0.58    u1_pre_topc(sK0) != u1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(superposition,[],[f47,f323])).
% 1.62/0.58  fof(f323,plain,(
% 1.62/0.58    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(global_subsumption,[],[f39,f38,f37,f36,f322])).
% 1.62/0.58  fof(f322,plain,(
% 1.62/0.58    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(forward_demodulation,[],[f318,f295])).
% 1.62/0.58  fof(f295,plain,(
% 1.62/0.58    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0))),
% 1.62/0.58    inference(backward_demodulation,[],[f230,f289])).
% 1.62/0.58  fof(f318,plain,(
% 1.62/0.58    u1_pre_topc(k6_tmap_1(sK0,k1_xboole_0)) = k5_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(superposition,[],[f46,f296])).
% 1.62/0.58  fof(f296,plain,(
% 1.62/0.58    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,k1_xboole_0) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(backward_demodulation,[],[f34,f294])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f132,plain,(
% 1.62/0.58    ~r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(global_subsumption,[],[f39,f129])).
% 1.62/0.58  fof(f129,plain,(
% 1.62/0.58    ~l1_pre_topc(sK0) | ~r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(resolution,[],[f43,f36])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f21])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f236,plain,(
% 1.62/0.58    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 1.62/0.58    inference(backward_demodulation,[],[f210,f229])).
% 1.62/0.58  fof(f229,plain,(
% 1.62/0.58    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f46])).
% 1.62/0.58  fof(f210,plain,(
% 1.62/0.58    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 1.62/0.58    inference(backward_demodulation,[],[f183,f196])).
% 1.62/0.58  fof(f196,plain,(
% 1.62/0.58    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f37,f38,f39,f36,f45])).
% 1.62/0.58  fof(f183,plain,(
% 1.62/0.58    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f159,f177,f41])).
% 1.62/0.58  fof(f177,plain,(
% 1.62/0.58    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f53])).
% 1.62/0.59  fof(f159,plain,(
% 1.62/0.59    v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f38,f37,f39,f36,f51])).
% 1.62/0.59  fof(f396,plain,(
% 1.62/0.59    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f395,f297])).
% 1.62/0.59  fof(f297,plain,(
% 1.62/0.59    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,k1_xboole_0) | ~v3_pre_topc(sK1,sK0)),
% 1.62/0.59    inference(backward_demodulation,[],[f35,f294])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f17])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (4835)------------------------------
% 1.62/0.59  % (4835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (4835)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (4835)Memory used [KB]: 6652
% 1.62/0.59  % (4835)Time elapsed: 0.163 s
% 1.62/0.59  % (4835)------------------------------
% 1.62/0.59  % (4835)------------------------------
% 1.62/0.59  % (4810)Success in time 0.221 s
%------------------------------------------------------------------------------
