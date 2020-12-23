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
% DateTime   : Thu Dec  3 13:12:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 342 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   26
%              Number of atoms          :  271 (1315 expanded)
%              Number of equality atoms :   56 ( 221 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(subsumption_resolution,[],[f273,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f273,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f171,f270])).

fof(f270,plain,(
    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(superposition,[],[f87,f255])).

fof(f255,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f254,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f241,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f241,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f240,f211])).

fof(f211,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f210,f51])).

fof(f210,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f168,f65])).

fof(f168,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f167,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    inference(resolution,[],[f166,f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f166,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f159,f65])).

fof(f159,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f157,f124])).

fof(f124,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f69,f118])).

fof(f118,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f116,f115])).

fof(f115,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f114,f43])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v3_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f55,f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

% (29256)Refutation not found, incomplete strategy% (29256)------------------------------
% (29256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

% (29256)Termination reason: Refutation not found, incomplete strategy

% (29256)Memory used [KB]: 10618
fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

% (29256)Time elapsed: 0.138 s
% (29256)------------------------------
% (29256)------------------------------
fof(f116,plain,(
    ! [X0] :
      ( ~ v2_tops_1(X0,sK0)
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f157,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(superposition,[],[f154,f87])).

fof(f154,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f62,f48])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f240,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f239,f48])).

fof(f239,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f237,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f237,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f235,f51])).

fof(f235,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f234,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v2_tops_1(X0,sK0)
      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f234,plain,(
    v2_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f233,f48])).

fof(f233,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f232,f51])).

fof(f232,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f58,f228])).

fof(f228,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f226,f118])).

fof(f226,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f215,f43])).

fof(f215,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f171,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f89,f170])).

fof(f170,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f169,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f164,f65])).

fof(f164,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f163,f151])).

fof(f151,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f149,f65])).

fof(f149,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f48])).

fof(f148,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f146,f57])).

fof(f146,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f145,f43])).

fof(f145,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f144,f115])).

fof(f163,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f162,f48])).

fof(f162,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f161,f54])).

fof(f161,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f160,f43])).

fof(f160,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f158,f65])).

fof(f158,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f155,f44])).

fof(f44,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f155,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f154,f89])).

fof(f89,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f66,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (29241)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.44  % (29241)Refutation not found, incomplete strategy% (29241)------------------------------
% 0.21/0.44  % (29241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (29257)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.45  % (29241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (29241)Memory used [KB]: 10746
% 0.21/0.45  % (29241)Time elapsed: 0.069 s
% 0.21/0.45  % (29241)------------------------------
% 0.21/0.45  % (29241)------------------------------
% 0.21/0.45  % (29249)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.45  % (29249)Refutation not found, incomplete strategy% (29249)------------------------------
% 0.21/0.45  % (29249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (29249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (29249)Memory used [KB]: 10618
% 0.21/0.46  % (29249)Time elapsed: 0.077 s
% 0.21/0.46  % (29249)------------------------------
% 0.21/0.46  % (29249)------------------------------
% 0.21/0.50  % (29240)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (29265)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (29239)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (29265)Refutation not found, incomplete strategy% (29265)------------------------------
% 0.21/0.51  % (29265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29251)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29244)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29247)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (29262)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29243)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29256)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (29245)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (29239)Refutation not found, incomplete strategy% (29239)------------------------------
% 0.21/0.52  % (29239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29250)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29254)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (29250)Refutation not found, incomplete strategy% (29250)------------------------------
% 0.21/0.53  % (29250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29250)Memory used [KB]: 10618
% 0.21/0.53  % (29250)Time elapsed: 0.125 s
% 0.21/0.53  % (29250)------------------------------
% 0.21/0.53  % (29250)------------------------------
% 0.21/0.53  % (29255)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29252)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (29260)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (29239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29248)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (29239)Memory used [KB]: 1663
% 0.21/0.53  % (29239)Time elapsed: 0.114 s
% 0.21/0.53  % (29239)------------------------------
% 0.21/0.53  % (29239)------------------------------
% 0.21/0.53  % (29268)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (29248)Refutation not found, incomplete strategy% (29248)------------------------------
% 0.21/0.53  % (29248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29265)Memory used [KB]: 10874
% 0.21/0.53  % (29265)Time elapsed: 0.117 s
% 0.21/0.53  % (29265)------------------------------
% 0.21/0.53  % (29265)------------------------------
% 0.21/0.53  % (29247)Refutation not found, incomplete strategy% (29247)------------------------------
% 0.21/0.53  % (29247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29247)Memory used [KB]: 10746
% 0.21/0.53  % (29247)Time elapsed: 0.130 s
% 0.21/0.53  % (29247)------------------------------
% 0.21/0.53  % (29247)------------------------------
% 0.21/0.53  % (29258)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29259)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (29245)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f273,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f19])).
% 0.21/0.53  fof(f19,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(backward_demodulation,[],[f171,f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.53    inference(superposition,[],[f87,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f254,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f241,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f240,f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f51])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f168,f65])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 0.21/0.53    inference(resolution,[],[f166,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f165,f51])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f159,f65])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    v3_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f48])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    v3_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(superposition,[],[f69,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f43])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f116,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    v2_tops_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f114,f43])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f113,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v3_tops_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f55,f48])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  % (29256)Refutation not found, incomplete strategy% (29256)------------------------------
% 0.21/0.53  % (29256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  % (29256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29256)Memory used [KB]: 10618
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.21/0.53  % (29256)Time elapsed: 0.138 s
% 0.21/0.53  % (29256)------------------------------
% 0.21/0.53  % (29256)------------------------------
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_tops_1(X0,sK0) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f59,f48])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(superposition,[],[f154,f87])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f62,f48])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f239,f48])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f237,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f235,f51])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f234,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_tops_1(X0,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f61,f48])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    v2_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f233,f48])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | v2_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f232,f51])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tops_1(k1_xboole_0,sK0)),
% 0.21/0.53    inference(superposition,[],[f58,f228])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(forward_demodulation,[],[f226,f118])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f215,f43])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f70,f48])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 0.21/0.53    inference(resolution,[],[f66,f51])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f89,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f43])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f164,f65])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f163,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f43])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f149,f65])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f48])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f146,f57])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f43])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f144,f115])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f162,f48])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(resolution,[],[f161,f54])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f160,f43])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f158,f65])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f155,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v3_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.53    inference(superposition,[],[f154,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.53    inference(resolution,[],[f66,f43])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (29245)------------------------------
% 0.21/0.53  % (29245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29245)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (29245)Memory used [KB]: 6396
% 0.21/0.53  % (29245)Time elapsed: 0.129 s
% 0.21/0.53  % (29245)------------------------------
% 0.21/0.53  % (29245)------------------------------
% 0.21/0.53  % (29242)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29237)Success in time 0.178 s
%------------------------------------------------------------------------------
