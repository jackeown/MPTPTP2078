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
% DateTime   : Thu Dec  3 13:21:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 959 expanded)
%              Number of leaves         :   18 ( 196 expanded)
%              Depth                    :   17
%              Number of atoms          :  407 (3720 expanded)
%              Number of equality atoms :   40 ( 228 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(subsumption_resolution,[],[f286,f284])).

fof(f284,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f229,f253])).

fof(f253,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f241,f252])).

fof(f252,plain,(
    sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f246])).

fof(f246,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f244,f234])).

fof(f234,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f232,f213])).

fof(f213,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f177,f82])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f44,f79])).

fof(f79,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f121,f176])).

fof(f176,plain,(
    ! [X0] : v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) ),
    inference(forward_demodulation,[],[f175,f79])).

fof(f175,plain,(
    ! [X0] : v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f174,plain,(
    ! [X0] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f109,f47])).

fof(f47,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    ! [X12,X11] :
      ( ~ v1_tdlat_3(X11)
      | v3_pre_topc(k4_xboole_0(u1_struct_0(X11),X12),X11)
      | ~ l1_pre_topc(X11) ) ),
    inference(resolution,[],[f83,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(subsumption_resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f83,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f121,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f120,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f71,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f120,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f119,f48])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(superposition,[],[f59,f79])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f232,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f100,f82])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(superposition,[],[f56,f79])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f244,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f113,f82])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f58,f79])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f251,plain,
    ( v1_tops_1(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f226,f141])).

fof(f141,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f85,f80])).

fof(f80,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f42,f79])).

fof(f42,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f68,f82])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f226,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f133,f82])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f132,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ v1_tdlat_3(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(X0,sK0)
      | ~ v1_tdlat_3(sK0) ) ),
    inference(superposition,[],[f76,f79])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_tex_2(X0,sK0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f131,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_tex_2(X0,sK0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_tex_2(X0,sK0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f129,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_tex_2(X0,sK0)
      | v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f62,f79])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f241,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f239,f234])).

fof(f239,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f103,f82])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f57,f79])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f229,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f140,f82])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f139,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f95,f48])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f94,f47])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(superposition,[],[f75,f79])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f61,f54])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f138,f45])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f137,f48])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(superposition,[],[f63,f79])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f286,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f256,f73])).

fof(f73,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f49,f50])).

% (16001)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f49,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f256,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f81,f252])).

fof(f81,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f43,f79])).

fof(f43,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (15998)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.43  % (15998)Refutation not found, incomplete strategy% (15998)------------------------------
% 0.22/0.43  % (15998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (15998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (15998)Memory used [KB]: 1663
% 0.22/0.43  % (15998)Time elapsed: 0.005 s
% 0.22/0.43  % (15998)------------------------------
% 0.22/0.43  % (15998)------------------------------
% 0.22/0.46  % (16002)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (16002)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f287,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f286,f284])).
% 0.22/0.46  fof(f284,plain,(
% 0.22/0.46    v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f229,f253])).
% 0.22/0.46  fof(f253,plain,(
% 0.22/0.46    v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f241,f252])).
% 0.22/0.46  fof(f252,plain,(
% 0.22/0.46    sK1 = k2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f251,f246])).
% 0.22/0.46  fof(f246,plain,(
% 0.22/0.46    sK1 = k2_struct_0(sK0) | ~v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(forward_demodulation,[],[f244,f234])).
% 0.22/0.46  fof(f234,plain,(
% 0.22/0.46    sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.46    inference(subsumption_resolution,[],[f232,f213])).
% 0.22/0.46  fof(f213,plain,(
% 0.22/0.46    v4_pre_topc(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f177,f82])).
% 0.22/0.46  fof(f82,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.46    inference(backward_demodulation,[],[f44,f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f52,f77])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    l1_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f53,f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    l1_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f18])).
% 0.22/0.46  fof(f18,conjecture,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f177,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f121,f176])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    ( ! [X0] : (v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0)) )),
% 0.22/0.46    inference(forward_demodulation,[],[f175,f79])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    ( ! [X0] : (v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f174,f48])).
% 0.22/0.46  fof(f174,plain,(
% 0.22/0.46    ( ! [X0] : (v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f109,f47])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    v1_tdlat_3(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f109,plain,(
% 0.22/0.46    ( ! [X12,X11] : (~v1_tdlat_3(X11) | v3_pre_topc(k4_xboole_0(u1_struct_0(X11),X12),X11) | ~l1_pre_topc(X11)) )),
% 0.22/0.46    inference(resolution,[],[f83,f76])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f64,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(resolution,[],[f70,f67])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.46    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.46  fof(f121,plain,(
% 0.22/0.46    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 0.22/0.46    inference(forward_demodulation,[],[f120,f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 0.22/0.46    inference(resolution,[],[f71,f74])).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f51,f50])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.46  fof(f120,plain,(
% 0.22/0.46    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f119,f48])).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f59,f79])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.22/0.46  fof(f232,plain,(
% 0.22/0.46    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.46    inference(resolution,[],[f100,f82])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f99,f48])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 0.22/0.46    inference(superposition,[],[f56,f79])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.46  fof(f244,plain,(
% 0.22/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f113,f82])).
% 0.22/0.46  fof(f113,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f112,f48])).
% 0.22/0.46  fof(f112,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f58,f79])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.46  fof(f251,plain,(
% 0.22/0.46    v1_tops_1(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f226,f141])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    v3_tex_2(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f85,f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    ~v1_subset_1(sK1,k2_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(backward_demodulation,[],[f42,f79])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f68,f82])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.46  fof(f226,plain,(
% 0.22/0.46    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f133,f82])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f132,f92])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f91,f47])).
% 0.22/0.46  fof(f91,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~v1_tdlat_3(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f90,f48])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0) | ~v1_tdlat_3(sK0)) )),
% 0.22/0.46    inference(superposition,[],[f76,f79])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f131,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ~v2_struct_0(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f130,f48])).
% 0.22/0.46  fof(f130,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f129,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    v2_pre_topc(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(X0,sK0) | ~v3_tex_2(X0,sK0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f62,f79])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.22/0.46  fof(f241,plain,(
% 0.22/0.46    sK1 != k2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(forward_demodulation,[],[f239,f234])).
% 0.22/0.46  fof(f239,plain,(
% 0.22/0.46    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f103,f82])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f102,f48])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f57,f79])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f229,plain,(
% 0.22/0.46    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f140,f82])).
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f139,f97])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f96,f45])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v2_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f95,f48])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f94,f47])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f75,f79])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f61,f54])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f138,f45])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f137,f48])).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f136,f46])).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.22/0.46    inference(superposition,[],[f63,f79])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,axiom,(
% 0.22/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.46  fof(f286,plain,(
% 0.22/0.46    ~v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f256,f73])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.22/0.46    inference(backward_demodulation,[],[f49,f50])).
% 0.22/0.46  % (16001)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.22/0.46  fof(f256,plain,(
% 0.22/0.46    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.46    inference(backward_demodulation,[],[f81,f252])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.46    inference(backward_demodulation,[],[f43,f79])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (16002)------------------------------
% 0.22/0.46  % (16002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (16002)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (16002)Memory used [KB]: 1791
% 0.22/0.46  % (16002)Time elapsed: 0.041 s
% 0.22/0.46  % (16002)------------------------------
% 0.22/0.46  % (16002)------------------------------
% 0.22/0.47  % (15984)Success in time 0.104 s
%------------------------------------------------------------------------------
