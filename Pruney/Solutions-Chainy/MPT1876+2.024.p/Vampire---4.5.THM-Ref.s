%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 (1831 expanded)
%              Number of leaves         :   15 ( 332 expanded)
%              Depth                    :   47
%              Number of atoms          :  528 (10711 expanded)
%              Number of equality atoms :   52 ( 311 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(subsumption_resolution,[],[f302,f274])).

fof(f274,plain,(
    l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f270,f170])).

fof(f170,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f167,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f166,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | l1_pre_topc(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f165,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | l1_pre_topc(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f157,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f157,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f156,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f156,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f155,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f58,f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f270,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f269,f42])).

fof(f269,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f268,f43])).

fof(f268,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f229,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f229,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | v2_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f116,f226])).

fof(f226,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f225,f42])).

fof(f225,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f223,f61])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = sK1
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(subsumption_resolution,[],[f221,f48])).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f221,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tarski(X0))
      | sK1 = k1_tarski(sK3(sK1))
      | k1_tarski(X0) = sK1
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f219,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f219,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = k1_tarski(sK3(sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f218,f42])).

fof(f218,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK3(sK1))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f216,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f216,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f215,f171])).

fof(f171,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f170,f40])).

fof(f40,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f215,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f214,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f214,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f213,f193])).

fof(f193,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f192,f40])).

fof(f192,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f191,f41])).

fof(f41,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f191,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f190,f44])).

fof(f190,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f188,f42])).

fof(f188,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f47])).

fof(f187,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f45])).

fof(f186,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f185,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f185,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f184,f40])).

fof(f184,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f183,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f182,f42])).

fof(f182,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f181,f43])).

fof(f181,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f180,f157])).

fof(f180,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f179,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f178,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f163,f46])).

fof(f46,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f163,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v1_zfmisc_1(sK1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2(sK0,sK1),X0)
      | v2_struct_0(sK2(sK0,sK1))
      | v7_struct_0(sK2(sK0,sK1))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f162,f69])).

% (6219)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f54,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f162,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f161,f40])).

fof(f161,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f42])).

fof(f158,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f154,f43])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f153,f44])).

fof(f153,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f152,f45])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f213,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(superposition,[],[f60,f212])).

fof(f212,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f211,f42])).

fof(f211,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f210,f61])).

fof(f210,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = sK1
      | sK1 = u1_struct_0(sK2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f208,f48])).

fof(f208,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tarski(X0))
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | k1_tarski(X0) = sK1
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f207,f64])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f206,f42])).

fof(f206,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f204,f49])).

fof(f204,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f203,f40])).

fof(f203,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f200,f42])).

fof(f200,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f198,f43])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f197,f47])).

fof(f197,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f194,f44])).

fof(f194,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f59,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f116,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f115,f95])).

fof(f95,plain,(
    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f92,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f77,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f77,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f63,f73])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f115,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f114,f44])).

fof(f114,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f302,plain,(
    ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f301,f50])).

fof(f301,plain,(
    ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f41,f270,f300])).

fof(f300,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f299,f272])).

fof(f272,plain,(
    v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f270,f192])).

fof(f299,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f60,f271])).

fof(f271,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f270,f203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:22:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (6217)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (6225)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (6217)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (6216)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (6215)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6214)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (6233)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (6233)Refutation not found, incomplete strategy% (6233)------------------------------
% 0.22/0.52  % (6233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f303,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f302,f274])).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f270,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f167,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~v1_xboole_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f16])).
% 0.22/0.52  fof(f16,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f166,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | l1_pre_topc(sK2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,X0))) )),
% 0.22/0.52    inference(resolution,[],[f157,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0] : (m1_pre_topc(sK2(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 0.22/0.52    inference(resolution,[],[f58,f47])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f269,f42])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f268,f43])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f229,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f68,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ~m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f116,f226])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f225,f42])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f224])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK3(sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f223,f61])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = sK1 | sK1 = k1_tarski(sK3(sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f221,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_tarski(X0)) | sK1 = k1_tarski(sK3(sK1)) | k1_tarski(X0) = sK1 | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f219,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = k1_tarski(sK3(sK1)) | sK1 = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f42])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 0.22/0.52    inference(resolution,[],[f216,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f215,f171])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f170,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1)) | ~l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f214,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f213,f193])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f192,f40])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f191,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f44])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f189,f43])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f188,f42])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f47])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f186,f45])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f185,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f184,f40])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f183,f41])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f182,f42])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f181,f43])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f180,f157])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f179,f44])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f47])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f163,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    v2_tdlat_3(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tdlat_3(X0) | v1_zfmisc_1(sK1) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f162,f69])).
% 0.22/0.52  % (6219)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f161,f40])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f158,f42])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f154,f43])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f44])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f45])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.22/0.52    inference(resolution,[],[f57,f47])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(superposition,[],[f60,f212])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f211,f42])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK3(sK1)) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f210,f61])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = sK1 | sK1 = u1_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f208,f48])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_tarski(X0)) | sK1 = u1_struct_0(sK2(sK0,sK1)) | k1_tarski(X0) = sK1 | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f207,f64])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f206,f42])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 0.22/0.52    inference(resolution,[],[f204,f49])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f203,f40])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f200,f42])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f198,f43])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f197,f47])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f194,f44])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.22/0.52    inference(resolution,[],[f59,f45])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    v2_tex_2(k1_tarski(sK3(sK1)),sK0) | ~m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.52    inference(superposition,[],[f115,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f42])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f78,f43])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3)) | v1_xboole_0(X3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X3] : (v1_xboole_0(X2) | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | v1_xboole_0(X3)) )),
% 0.22/0.52    inference(resolution,[],[f63,f73])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f44])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f113,f45])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.52    inference(resolution,[],[f55,f47])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    ~l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f301,f50])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(global_subsumption,[],[f41,f270,f300])).
% 0.22/0.52  fof(f300,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f299,f272])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f270,f192])).
% 0.22/0.52  fof(f299,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f60,f271])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f270,f203])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6217)------------------------------
% 0.22/0.52  % (6217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6217)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6217)Memory used [KB]: 6524
% 0.22/0.52  % (6217)Time elapsed: 0.096 s
% 0.22/0.52  % (6217)------------------------------
% 0.22/0.52  % (6217)------------------------------
% 0.22/0.52  % (6210)Success in time 0.157 s
%------------------------------------------------------------------------------
