%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:53 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 413 expanded)
%              Number of leaves         :   15 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  187 (1319 expanded)
%              Number of equality atoms :   48 ( 272 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(global_subsumption,[],[f33,f241])).

fof(f241,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f234,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f64,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f53,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f55,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f234,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f94,f231])).

fof(f231,plain,(
    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(global_subsumption,[],[f35,f73,f139,f230])).

fof(f230,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f224,f58])).

fof(f58,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f56,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f224,plain,
    ( k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f214,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

% (9109)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f214,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f73,f213,f113])).

fof(f113,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X2,sK0)
      | k2_pre_topc(sK0,X2) = X2 ) ),
    inference(global_subsumption,[],[f35,f112])).

fof(f112,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v4_pre_topc(X2,sK0)
      | k2_pre_topc(sK0,X2) = X2 ) ),
    inference(superposition,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f213,plain,(
    v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f31,f73,f206])).

fof(f206,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f189,f94])).

fof(f189,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X2,sK0) ) ),
    inference(global_subsumption,[],[f35,f183])).

fof(f183,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(X2,sK0) ) ),
    inference(superposition,[],[f47,f58])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f31,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f139,plain,(
    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f131,f65])).

fof(f65,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f60,f51])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f58])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f32,f60,f130])).

fof(f130,plain,(
    ! [X2] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_tops_1(X2,sK0) ) ),
    inference(global_subsumption,[],[f35,f124])).

fof(f124,plain,(
    ! [X2] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_tops_1(X2,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f44,f58])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f32,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f62,f65])).

fof(f62,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f87,f65])).

fof(f87,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (9092)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (9100)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (9118)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (9100)Refutation not found, incomplete strategy% (9100)------------------------------
% 0.22/0.51  % (9100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9100)Memory used [KB]: 10746
% 0.22/0.51  % (9100)Time elapsed: 0.086 s
% 0.22/0.51  % (9100)------------------------------
% 0.22/0.51  % (9100)------------------------------
% 0.22/0.52  % (9110)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (9118)Refutation not found, incomplete strategy% (9118)------------------------------
% 0.22/0.53  % (9118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (9116)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (9102)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (9118)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (9118)Memory used [KB]: 10746
% 1.36/0.54  % (9118)Time elapsed: 0.114 s
% 1.36/0.54  % (9118)------------------------------
% 1.36/0.54  % (9118)------------------------------
% 1.36/0.55  % (9102)Refutation not found, incomplete strategy% (9102)------------------------------
% 1.36/0.55  % (9102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (9102)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (9102)Memory used [KB]: 10618
% 1.36/0.55  % (9102)Time elapsed: 0.130 s
% 1.36/0.55  % (9102)------------------------------
% 1.36/0.55  % (9102)------------------------------
% 1.36/0.55  % (9105)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (9106)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (9101)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (9094)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (9121)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (9097)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.55  % (9094)Refutation not found, incomplete strategy% (9094)------------------------------
% 1.50/0.55  % (9094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (9094)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (9094)Memory used [KB]: 10874
% 1.50/0.55  % (9094)Time elapsed: 0.120 s
% 1.50/0.55  % (9094)------------------------------
% 1.50/0.55  % (9094)------------------------------
% 1.50/0.56  % (9114)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.56  % (9096)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.56  % (9113)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.56  % (9099)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.56  % (9113)Refutation not found, incomplete strategy% (9113)------------------------------
% 1.50/0.56  % (9113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (9113)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (9113)Memory used [KB]: 1791
% 1.50/0.56  % (9113)Time elapsed: 0.121 s
% 1.50/0.56  % (9113)------------------------------
% 1.50/0.56  % (9113)------------------------------
% 1.50/0.56  % (9116)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % (9108)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.56  % (9095)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f242,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(global_subsumption,[],[f33,f241])).
% 1.50/0.56  fof(f241,plain,(
% 1.50/0.56    k1_xboole_0 = sK1),
% 1.50/0.56    inference(forward_demodulation,[],[f234,f74])).
% 1.50/0.56  fof(f74,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.50/0.56    inference(forward_demodulation,[],[f64,f54])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.50/0.56    inference(backward_demodulation,[],[f53,f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f37,f49])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f55,f51])).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.50/0.56    inference(forward_demodulation,[],[f39,f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.50/0.56  fof(f234,plain,(
% 1.50/0.56    sK1 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.50/0.56    inference(backward_demodulation,[],[f94,f231])).
% 1.50/0.56  fof(f231,plain,(
% 1.50/0.56    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 1.50/0.56    inference(global_subsumption,[],[f35,f73,f139,f230])).
% 1.50/0.56  fof(f230,plain,(
% 1.50/0.56    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1) | ~l1_pre_topc(sK0) | ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.56    inference(forward_demodulation,[],[f224,f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f56,f40])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    l1_struct_0(sK0)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f35,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.50/0.56  fof(f224,plain,(
% 1.50/0.56    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.56    inference(superposition,[],[f214,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tops_1(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.50/0.56  % (9109)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  fof(f214,plain,(
% 1.50/0.56    k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f73,f213,f113])).
% 1.50/0.56  fof(f113,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X2,sK0) | k2_pre_topc(sK0,X2) = X2) )),
% 1.50/0.56    inference(global_subsumption,[],[f35,f112])).
% 1.50/0.56  fof(f112,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X2,sK0) | k2_pre_topc(sK0,X2) = X2) )),
% 1.50/0.56    inference(superposition,[],[f43,f58])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.50/0.57  fof(f213,plain,(
% 1.50/0.57    v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.57    inference(global_subsumption,[],[f31,f73,f206])).
% 1.50/0.57  fof(f206,plain,(
% 1.50/0.57    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.57    inference(superposition,[],[f189,f94])).
% 1.50/0.57  fof(f189,plain,(
% 1.50/0.57    ( ! [X2] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X2,sK0)) )),
% 1.50/0.57    inference(global_subsumption,[],[f35,f183])).
% 1.50/0.57  fof(f183,plain,(
% 1.50/0.57    ( ! [X2] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(X2,sK0)) )),
% 1.50/0.57    inference(superposition,[],[f47,f58])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f26])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,axiom,(
% 1.50/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    v3_pre_topc(sK1,sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.50/0.57    inference(flattening,[],[f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,negated_conjecture,(
% 1.50/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.50/0.57    inference(negated_conjecture,[],[f15])).
% 1.50/0.57  fof(f15,conjecture,(
% 1.50/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 1.50/0.57  fof(f139,plain,(
% 1.50/0.57    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.57    inference(forward_demodulation,[],[f131,f65])).
% 1.50/0.57  fof(f65,plain,(
% 1.50/0.57    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f60,f51])).
% 1.50/0.57  fof(f60,plain,(
% 1.50/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f30,f58])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f131,plain,(
% 1.50/0.57    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f32,f60,f130])).
% 1.50/0.57  fof(f130,plain,(
% 1.50/0.57    ( ! [X2] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tops_1(X2,sK0)) )),
% 1.50/0.57    inference(global_subsumption,[],[f35,f124])).
% 1.50/0.57  fof(f124,plain,(
% 1.50/0.57    ( ! [X2] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tops_1(X2,sK0) | ~l1_pre_topc(sK0)) )),
% 1.50/0.57    inference(superposition,[],[f44,f58])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.57    inference(flattening,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,axiom,(
% 1.50/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    v3_tops_1(sK1,sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f73,plain,(
% 1.50/0.57    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.50/0.57    inference(backward_demodulation,[],[f62,f65])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f60,f50])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f27])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    l1_pre_topc(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f94,plain,(
% 1.50/0.57    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.50/0.57    inference(forward_demodulation,[],[f87,f65])).
% 1.50/0.57  fof(f87,plain,(
% 1.50/0.57    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f60,f52])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    k1_xboole_0 != sK1),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (9116)------------------------------
% 1.50/0.57  % (9116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (9116)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (9116)Memory used [KB]: 6396
% 1.50/0.57  % (9116)Time elapsed: 0.139 s
% 1.50/0.57  % (9116)------------------------------
% 1.50/0.57  % (9116)------------------------------
% 1.50/0.57  % (9098)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.57  % (9109)Refutation not found, incomplete strategy% (9109)------------------------------
% 1.50/0.57  % (9109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (9109)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (9109)Memory used [KB]: 10618
% 1.50/0.57  % (9109)Time elapsed: 0.156 s
% 1.50/0.57  % (9109)------------------------------
% 1.50/0.57  % (9109)------------------------------
% 1.50/0.57  % (9091)Success in time 0.194 s
%------------------------------------------------------------------------------
