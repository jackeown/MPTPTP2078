%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  132 (5761 expanded)
%              Number of leaves         :   18 (1556 expanded)
%              Depth                    :   23
%              Number of atoms          :  530 (36565 expanded)
%              Number of equality atoms :   60 ( 795 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f290,f311])).

fof(f311,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f275,f310])).

fof(f310,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f217,f268])).

fof(f268,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f116,f267])).

fof(f267,plain,(
    sK1 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( sK1 = k2_struct_0(sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(superposition,[],[f257,f158])).

fof(f158,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,X0) = X0 ),
    inference(backward_demodulation,[],[f127,f144])).

fof(f144,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f136,f135])).

fof(f135,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f64,f116,f132,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f132,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f115,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f115,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f64,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f136,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f64,f116,f132,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f127,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f257,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(superposition,[],[f245,f236])).

fof(f236,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f232,f230])).

fof(f230,plain,
    ( v1_tops_1(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f215,f226])).

fof(f226,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f222,f126])).

fof(f126,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f62,f64,f63,f65,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f63,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f222,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f149,f145])).

fof(f145,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f65,f144])).

fof(f149,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | v1_tops_1(X1,sK0) ) ),
    inference(backward_demodulation,[],[f106,f144])).

fof(f106,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f105,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f64])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_tops_1(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f215,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f167,f146])).

fof(f146,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f66,f144])).

fof(f66,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f167,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f160,f144])).

fof(f160,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(backward_demodulation,[],[f131,f144])).

fof(f131,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f232,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f166,f145])).

fof(f166,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)
      | ~ v1_tops_1(X2,sK0) ) ),
    inference(forward_demodulation,[],[f156,f144])).

fof(f156,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X2) ) ),
    inference(backward_demodulation,[],[f121,f144])).

fof(f121,plain,(
    ! [X2] :
      ( ~ v1_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = k2_pre_topc(sK0,X2) ) ),
    inference(resolution,[],[f64,f74])).

fof(f245,plain,(
    sK1 = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f159,f145,f161,f164])).

fof(f164,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | k9_subset_1(k2_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f163,f144])).

fof(f163,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f151,f144])).

fof(f151,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f112,f144])).

fof(f112,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f111,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f103,f61])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f63])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tdlat_3(sK0)
      | v2_tex_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f64])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | v2_tex_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f111,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f110,f61])).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f64])).

fof(f98,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1)))
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f161,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f132,f144])).

fof(f159,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f128,f144])).

fof(f128,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f64,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_1(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).

fof(f217,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f150,f145])).

fof(f150,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | v3_tex_2(X2,sK0) ) ),
    inference(backward_demodulation,[],[f109,f144])).

fof(f109,plain,(
    ! [X2] :
      ( ~ v1_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f108,f104])).

fof(f108,plain,(
    ! [X2] :
      ( ~ v2_tex_2(X2,sK0)
      | ~ v1_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f107,f61])).

fof(f107,plain,(
    ! [X2] :
      ( ~ v2_tex_2(X2,sK0)
      | ~ v1_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X2,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f64])).

fof(f97,plain,(
    ! [X2] :
      ( ~ v2_tex_2(X2,sK0)
      | ~ v1_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v3_tex_2(X2,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f275,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f147,f267])).

fof(f147,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f67,f144])).

fof(f67,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f290,plain,(
    ~ v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f184,f267])).

fof(f184,plain,(
    ~ v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f161,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:54:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.40  % (24280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.41  % (24280)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f316,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(subsumption_resolution,[],[f290,f311])).
% 0.19/0.41  fof(f311,plain,(
% 0.19/0.41    v1_subset_1(sK1,sK1)),
% 0.19/0.41    inference(subsumption_resolution,[],[f275,f310])).
% 0.19/0.41  fof(f310,plain,(
% 0.19/0.41    v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(global_subsumption,[],[f217,f268])).
% 0.19/0.41  fof(f268,plain,(
% 0.19/0.41    v1_tops_1(sK1,sK0)),
% 0.19/0.41    inference(backward_demodulation,[],[f116,f267])).
% 0.19/0.41  fof(f267,plain,(
% 0.19/0.41    sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(duplicate_literal_removal,[],[f264])).
% 0.19/0.41  fof(f264,plain,(
% 0.19/0.41    sK1 = k2_struct_0(sK0) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(superposition,[],[f257,f158])).
% 0.19/0.41  fof(f158,plain,(
% 0.19/0.41    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,X0) = X0) )),
% 0.19/0.41    inference(backward_demodulation,[],[f127,f144])).
% 0.19/0.41  fof(f144,plain,(
% 0.19/0.41    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.41    inference(backward_demodulation,[],[f136,f135])).
% 0.19/0.41  fof(f135,plain,(
% 0.19/0.41    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f64,f116,f132,f72])).
% 0.19/0.41  fof(f72,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f47])).
% 0.19/0.41  fof(f47,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(nnf_transformation,[],[f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.19/0.41  fof(f132,plain,(
% 0.19/0.41    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f115,f68])).
% 0.19/0.41  fof(f68,plain,(
% 0.19/0.41    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.19/0.41  fof(f115,plain,(
% 0.19/0.41    l1_struct_0(sK0)),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f64,f69])).
% 0.19/0.41  fof(f69,plain,(
% 0.19/0.41    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.41  fof(f64,plain,(
% 0.19/0.41    l1_pre_topc(sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f46,plain,(
% 0.19/0.41    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f45,plain,(
% 0.19/0.41    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f43,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f42])).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.41    inference(nnf_transformation,[],[f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f18])).
% 0.19/0.41  fof(f18,negated_conjecture,(
% 0.19/0.41    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.19/0.41    inference(negated_conjecture,[],[f17])).
% 0.19/0.41  fof(f17,conjecture,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.19/0.41  fof(f136,plain,(
% 0.19/0.41    u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f64,f116,f132,f74])).
% 0.19/0.41  fof(f74,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(nnf_transformation,[],[f27])).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,axiom,(
% 0.19/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.19/0.41  fof(f127,plain,(
% 0.19/0.41    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,X0) = X0) )),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f65,f93])).
% 0.19/0.41  fof(f93,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.19/0.41    inference(cnf_transformation,[],[f41])).
% 0.19/0.41  fof(f41,plain,(
% 0.19/0.41    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.19/0.41  fof(f65,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f257,plain,(
% 0.19/0.41    sK1 = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(superposition,[],[f245,f236])).
% 0.19/0.41  fof(f236,plain,(
% 0.19/0.41    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(resolution,[],[f232,f230])).
% 0.19/0.41  fof(f230,plain,(
% 0.19/0.41    v1_tops_1(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(resolution,[],[f215,f226])).
% 0.19/0.41  fof(f226,plain,(
% 0.19/0.41    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.19/0.41    inference(subsumption_resolution,[],[f222,f126])).
% 0.19/0.41  fof(f126,plain,(
% 0.19/0.41    v3_pre_topc(sK1,sK0)),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f62,f64,f63,f65,f84])).
% 0.19/0.41  fof(f84,plain,(
% 0.19/0.41    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f56])).
% 0.19/0.41  fof(f56,plain,(
% 0.19/0.41    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 0.19/0.41  fof(f55,plain,(
% 0.19/0.41    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.41    inference(rectify,[],[f53])).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.41    inference(nnf_transformation,[],[f39])).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.41    inference(flattening,[],[f38])).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,axiom,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.19/0.41  fof(f63,plain,(
% 0.19/0.41    v1_tdlat_3(sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f62,plain,(
% 0.19/0.41    v2_pre_topc(sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f222,plain,(
% 0.19/0.41    ~v3_tex_2(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.19/0.41    inference(resolution,[],[f149,f145])).
% 0.19/0.41  fof(f145,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.41    inference(backward_demodulation,[],[f65,f144])).
% 0.19/0.41  fof(f149,plain,(
% 0.19/0.41    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0) | v1_tops_1(X1,sK0)) )),
% 0.19/0.41    inference(backward_demodulation,[],[f106,f144])).
% 0.19/0.41  fof(f106,plain,(
% 0.19/0.41    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f105,f61])).
% 0.19/0.41  fof(f61,plain,(
% 0.19/0.41    ~v2_struct_0(sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f105,plain,(
% 0.19/0.41    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f96,f64])).
% 0.19/0.41  fof(f96,plain,(
% 0.19/0.41    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(X1,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(resolution,[],[f62,f78])).
% 0.19/0.41  fof(f78,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f33])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f32])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f15])).
% 0.19/0.41  fof(f15,axiom,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.19/0.41  fof(f215,plain,(
% 0.19/0.41    v3_tex_2(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(resolution,[],[f167,f146])).
% 0.19/0.41  fof(f146,plain,(
% 0.19/0.41    ~v1_subset_1(sK1,k2_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(backward_demodulation,[],[f66,f144])).
% 0.19/0.41  fof(f66,plain,(
% 0.19/0.41    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f167,plain,(
% 0.19/0.41    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 0.19/0.41    inference(forward_demodulation,[],[f160,f144])).
% 0.19/0.41  fof(f160,plain,(
% 0.19/0.41    v1_subset_1(sK1,k2_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 0.19/0.41    inference(backward_demodulation,[],[f131,f144])).
% 0.19/0.41  fof(f131,plain,(
% 0.19/0.41    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.41    inference(resolution,[],[f65,f90])).
% 0.19/0.41  fof(f90,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f59])).
% 0.19/0.41  fof(f59,plain,(
% 0.19/0.41    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(nnf_transformation,[],[f40])).
% 0.19/0.41  fof(f40,plain,(
% 0.19/0.41    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.19/0.41  fof(f232,plain,(
% 0.19/0.41    ~v1_tops_1(sK1,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.19/0.41    inference(resolution,[],[f166,f145])).
% 0.19/0.41  fof(f166,plain,(
% 0.19/0.41    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) | ~v1_tops_1(X2,sK0)) )),
% 0.19/0.41    inference(forward_demodulation,[],[f156,f144])).
% 0.19/0.41  fof(f156,plain,(
% 0.19/0.41    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,X2)) )),
% 0.19/0.41    inference(backward_demodulation,[],[f121,f144])).
% 0.19/0.41  fof(f121,plain,(
% 0.19/0.41    ( ! [X2] : (~v1_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,X2)) )),
% 0.19/0.41    inference(resolution,[],[f64,f74])).
% 0.19/0.41  fof(f245,plain,(
% 0.19/0.41    sK1 = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f159,f145,f161,f164])).
% 0.19/0.41  fof(f164,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | k9_subset_1(k2_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4)) )),
% 0.19/0.41    inference(forward_demodulation,[],[f163,f144])).
% 0.19/0.41  fof(f163,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3) )),
% 0.19/0.41    inference(forward_demodulation,[],[f151,f144])).
% 0.19/0.41  fof(f151,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3) )),
% 0.19/0.41    inference(backward_demodulation,[],[f112,f144])).
% 0.19/0.41  fof(f112,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f111,f104])).
% 0.19/0.41  fof(f104,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f103,f61])).
% 0.19/0.41  fof(f103,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f102,f63])).
% 0.19/0.41  fof(f102,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f95,f64])).
% 0.19/0.41  fof(f95,plain,(
% 0.19/0.41    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(resolution,[],[f62,f77])).
% 0.19/0.41  fof(f77,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f31])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f30])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,axiom,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.19/0.41  fof(f111,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f110,f61])).
% 0.19/0.41  fof(f110,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f98,f64])).
% 0.19/0.41  fof(f98,plain,(
% 0.19/0.41    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,X3)) = X3 | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(resolution,[],[f62,f80])).
% 0.19/0.41  fof(f80,plain,(
% 0.19/0.41    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f52])).
% 0.19/0.41  fof(f52,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f50,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(rectify,[],[f49])).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(nnf_transformation,[],[f37])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f36])).
% 0.19/0.41  fof(f36,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f13])).
% 0.19/0.41  fof(f13,axiom,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.19/0.41  fof(f161,plain,(
% 0.19/0.41    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.41    inference(backward_demodulation,[],[f132,f144])).
% 0.19/0.41  fof(f159,plain,(
% 0.19/0.41    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.19/0.41    inference(backward_demodulation,[],[f128,f144])).
% 0.19/0.41  fof(f128,plain,(
% 0.19/0.41    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f65,f91])).
% 0.19/0.41  fof(f91,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f60])).
% 0.19/0.41  fof(f60,plain,(
% 0.19/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.41    inference(nnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.41  fof(f116,plain,(
% 0.19/0.41    v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f64,f70])).
% 0.19/0.41  fof(f70,plain,(
% 0.19/0.41    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_1(k2_struct_0(X0),X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0] : (l1_pre_topc(X0) => v1_tops_1(k2_struct_0(X0),X0))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).
% 0.19/0.41  fof(f217,plain,(
% 0.19/0.41    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0)),
% 0.19/0.41    inference(resolution,[],[f150,f145])).
% 0.19/0.41  fof(f150,plain,(
% 0.19/0.41    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | v3_tex_2(X2,sK0)) )),
% 0.19/0.41    inference(backward_demodulation,[],[f109,f144])).
% 0.19/0.41  fof(f109,plain,(
% 0.19/0.41    ( ! [X2] : (~v1_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X2,sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f108,f104])).
% 0.19/0.41  fof(f108,plain,(
% 0.19/0.41    ( ! [X2] : (~v2_tex_2(X2,sK0) | ~v1_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X2,sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f107,f61])).
% 0.19/0.41  fof(f107,plain,(
% 0.19/0.41    ( ! [X2] : (~v2_tex_2(X2,sK0) | ~v1_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X2,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(subsumption_resolution,[],[f97,f64])).
% 0.19/0.41  fof(f97,plain,(
% 0.19/0.41    ( ! [X2] : (~v2_tex_2(X2,sK0) | ~v1_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_tex_2(X2,sK0) | v2_struct_0(sK0)) )),
% 0.19/0.41    inference(resolution,[],[f62,f79])).
% 0.19/0.41  fof(f79,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f35])).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.41    inference(flattening,[],[f34])).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f16])).
% 0.19/0.41  fof(f16,axiom,(
% 0.19/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.19/0.41  fof(f275,plain,(
% 0.19/0.41    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(backward_demodulation,[],[f147,f267])).
% 0.19/0.41  fof(f147,plain,(
% 0.19/0.41    v1_subset_1(sK1,k2_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(backward_demodulation,[],[f67,f144])).
% 0.19/0.41  fof(f67,plain,(
% 0.19/0.41    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f46])).
% 0.19/0.41  fof(f290,plain,(
% 0.19/0.41    ~v1_subset_1(sK1,sK1)),
% 0.19/0.41    inference(backward_demodulation,[],[f184,f267])).
% 0.19/0.41  fof(f184,plain,(
% 0.19/0.41    ~v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f161,f94])).
% 0.19/0.41  fof(f94,plain,(
% 0.19/0.41    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.19/0.41    inference(equality_resolution,[],[f89])).
% 0.19/0.41  fof(f89,plain,(
% 0.19/0.41    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f59])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (24280)------------------------------
% 0.19/0.41  % (24280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (24280)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (24280)Memory used [KB]: 6268
% 0.19/0.41  % (24280)Time elapsed: 0.014 s
% 0.19/0.41  % (24280)------------------------------
% 0.19/0.41  % (24280)------------------------------
% 0.19/0.42  % (24264)Success in time 0.083 s
%------------------------------------------------------------------------------
