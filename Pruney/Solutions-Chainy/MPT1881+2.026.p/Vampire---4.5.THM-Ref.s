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
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 578 expanded)
%              Number of leaves         :   35 ( 166 expanded)
%              Depth                    :   21
%              Number of atoms          :  765 (3383 expanded)
%              Number of equality atoms :   52 ( 109 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f242,f305,f322,f367,f393,f397,f491,f604])).

% (16910)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f604,plain,
    ( spl11_2
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl11_2
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f602,f330])).

fof(f330,plain,
    ( ~ v3_tex_2(sK7,sK6)
    | spl11_2 ),
    inference(global_subsumption,[],[f79,f134])).

fof(f134,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl11_2
  <=> v1_subset_1(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f79,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ v3_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( v1_subset_1(sK7,u1_struct_0(sK6))
      | ~ v3_tex_2(sK7,sK6) )
    & ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
      | v3_tex_2(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v1_tdlat_3(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).

fof(f50,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK6))
            | ~ v3_tex_2(X1,sK6) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK6))
            | v3_tex_2(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v1_tdlat_3(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK6))
          | ~ v3_tex_2(X1,sK6) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK6))
          | v3_tex_2(X1,sK6) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( v1_subset_1(sK7,u1_struct_0(sK6))
        | ~ v3_tex_2(sK7,sK6) )
      & ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
        | v3_tex_2(sK7,sK6) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f602,plain,
    ( v3_tex_2(sK7,sK6)
    | spl11_2
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f598,f288])).

fof(f288,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl11_5
  <=> v1_tops_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f598,plain,
    ( ~ v1_tops_1(sK7,sK6)
    | v3_tex_2(sK7,sK6)
    | spl11_2
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(resolution,[],[f597,f119])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f81,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f597,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v1_tops_1(X0,sK6)
        | v3_tex_2(X0,sK6) )
    | spl11_2
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f596,f205])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v2_tex_2(X0,sK6) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f204,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v2_tex_2(X0,sK6)
        | v2_struct_0(sK6) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f203,f75])).

fof(f75,plain,(
    v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v2_tex_2(X0,sK6)
        | ~ v1_tdlat_3(sK6)
        | v2_struct_0(sK6) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f201,f76])).

fof(f76,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v2_tex_2(X0,sK6)
        | ~ l1_pre_topc(sK6)
        | ~ v1_tdlat_3(sK6)
        | v2_struct_0(sK6) )
    | spl11_2 ),
    inference(superposition,[],[f120,f161])).

fof(f161,plain,
    ( u1_struct_0(sK6) = sK7
    | spl11_2 ),
    inference(subsumption_resolution,[],[f158,f134])).

fof(f158,plain,
    ( u1_struct_0(sK6) = sK7
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(resolution,[],[f111,f77])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f596,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v2_tex_2(X0,sK6)
        | ~ v1_tops_1(X0,sK6)
        | v3_tex_2(X0,sK6) )
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f595,f73])).

fof(f595,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v2_tex_2(X0,sK6)
        | ~ v1_tops_1(X0,sK6)
        | v3_tex_2(X0,sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f594,f74])).

fof(f74,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f594,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v2_tex_2(X0,sK6)
        | ~ v1_tops_1(X0,sK6)
        | v3_tex_2(X0,sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f592,f76])).

fof(f592,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v2_tex_2(X0,sK6)
        | ~ v1_tops_1(X0,sK6)
        | v3_tex_2(X0,sK6)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(superposition,[],[f102,f499])).

fof(f499,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f498,f237])).

fof(f237,plain,
    ( sK7 = k2_pre_topc(sK6,sK7)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl11_3
  <=> sK7 = k2_pre_topc(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f498,plain,
    ( u1_struct_0(sK6) = k2_pre_topc(sK6,sK7)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f497,f76])).

fof(f497,plain,
    ( u1_struct_0(sK6) = k2_pre_topc(sK6,sK7)
    | ~ l1_pre_topc(sK6)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f306,f288])).

fof(f306,plain,
    ( ~ v1_tops_1(sK7,sK6)
    | u1_struct_0(sK6) = k2_pre_topc(sK6,sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f77,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f491,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f489,f118])).

fof(f118,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f80,f81])).

fof(f80,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f489,plain,
    ( v1_subset_1(sK7,sK7)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(forward_demodulation,[],[f133,f464])).

fof(f464,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f463,f73])).

fof(f463,plain,
    ( u1_struct_0(sK6) = sK7
    | v2_struct_0(sK6)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f462,f75])).

fof(f462,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ v1_tdlat_3(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f461,f76])).

fof(f461,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ l1_pre_topc(sK6)
    | ~ v1_tdlat_3(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f454,f381])).

fof(f381,plain,
    ( sP0(sK7,sK6)
    | ~ spl11_6 ),
    inference(resolution,[],[f321,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f321,plain,
    ( sP1(sK6,sK7)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl11_6
  <=> sP1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f454,plain,
    ( u1_struct_0(sK6) = sK7
    | ~ sP0(sK7,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v1_tdlat_3(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_8 ),
    inference(resolution,[],[f447,f392])).

fof(f392,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl11_8
  <=> r1_tarski(sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | u1_struct_0(X1) = X0
      | ~ sP0(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f437,f196])).

fof(f196,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f120,f119])).

fof(f437,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | u1_struct_0(X1) = X0
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f93,f119])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | X0 = X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK8(X0,X1) != X0
          & r1_tarski(X0,sK8(X0,X1))
          & v2_tex_2(sK8(X0,X1),X1)
          & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK8(X0,X1) != X0
        & r1_tarski(X0,sK8(X0,X1))
        & v2_tex_2(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f133,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f397,plain,(
    ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl11_7 ),
    inference(resolution,[],[f395,f388])).

fof(f388,plain,
    ( sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl11_7
  <=> sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f395,plain,(
    ! [X0] : ~ sP5(u1_struct_0(sK6),sK7,X0) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X0] :
      ( ~ sP5(u1_struct_0(sK6),sK7,X0)
      | ~ sP5(u1_struct_0(sK6),sK7,X0) ) ),
    inference(resolution,[],[f384,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(sK10(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X1)
        & m1_subset_1(sK10(X0,X1,X2),X2) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
     => ( ~ r2_hidden(sK10(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X1)
        & m1_subset_1(sK10(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP5(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f384,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(u1_struct_0(sK6),X0,X1),sK7)
      | ~ sP5(u1_struct_0(sK6),X0,X1) ) ),
    inference(resolution,[],[f313,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f313,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK6))
      | ~ r2_hidden(X1,sK7) ) ),
    inference(resolution,[],[f77,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f393,plain,
    ( spl11_7
    | spl11_8 ),
    inference(avatar_split_clause,[],[f311,f390,f386])).

fof(f311,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6))
    | sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6)) ),
    inference(resolution,[],[f77,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X0)
      | sP5(X0,X1,X0) ) ),
    inference(resolution,[],[f116,f119])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP5(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | sP5(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f38,f46])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f367,plain,
    ( spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(subsumption_resolution,[],[f365,f119])).

fof(f365,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(forward_demodulation,[],[f364,f161])).

fof(f364,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(subsumption_resolution,[],[f363,f76])).

fof(f363,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(subsumption_resolution,[],[f362,f289])).

fof(f289,plain,
    ( ~ v1_tops_1(sK7,sK6)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f287])).

fof(f362,plain,
    ( v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f361,f161])).

fof(f361,plain,
    ( u1_struct_0(sK6) != sK7
    | v1_tops_1(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | ~ spl11_3 ),
    inference(superposition,[],[f87,f237])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f322,plain,
    ( spl11_6
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f143,f128,f319])).

fof(f128,plain,
    ( spl11_1
  <=> v3_tex_2(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f143,plain,
    ( ~ v3_tex_2(sK7,sK6)
    | sP1(sK6,sK7) ),
    inference(resolution,[],[f141,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f141,plain,(
    sP2(sK7,sK6) ),
    inference(subsumption_resolution,[],[f138,f76])).

fof(f138,plain,
    ( sP2(sK7,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f98,f77])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f41,f40,f39])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f305,plain,
    ( spl11_2
    | spl11_4 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl11_2
    | spl11_4 ),
    inference(subsumption_resolution,[],[f300,f241])).

fof(f241,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl11_4
  <=> v4_pre_topc(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f300,plain,
    ( v4_pre_topc(sK7,sK6)
    | spl11_2 ),
    inference(resolution,[],[f299,f119])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v4_pre_topc(X0,sK6) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f298,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_subset_1(sK7,X0),sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK7)) )
    | spl11_2 ),
    inference(resolution,[],[f170,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v3_pre_topc(X0,sK6) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f165,f126])).

fof(f126,plain,(
    sP3(sK6) ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f125,plain,
    ( ~ v1_tdlat_3(sK6)
    | sP3(sK6) ),
    inference(resolution,[],[f123,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ sP4(X0)
      | ~ v1_tdlat_3(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ~ sP3(X0) )
        & ( sP3(X0)
          | ~ v1_tdlat_3(X0) ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> sP3(X0) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f123,plain,(
    sP4(sK6) ),
    inference(subsumption_resolution,[],[f122,f76])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK6)
    | sP4(sK6) ),
    inference(resolution,[],[f108,f74])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f33,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP3(X0)
    <=> ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | v3_pre_topc(X0,sK6)
        | ~ sP3(sK6) )
    | spl11_2 ),
    inference(superposition,[],[f105,f161])).

fof(f105,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ( ~ v3_pre_topc(sK9(X0),X0)
          & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK9(X0),X0)
        & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(sK7,X0),sK6)
        | v4_pre_topc(X0,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK7)) )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f295,f76])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(sK7,X0),sK6)
        | v4_pre_topc(X0,sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ l1_pre_topc(sK6) )
    | spl11_2 ),
    inference(superposition,[],[f100,f161])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f242,plain,
    ( spl11_3
    | ~ spl11_4
    | spl11_2 ),
    inference(avatar_split_clause,[],[f230,f132,f239,f235])).

fof(f230,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | sK7 = k2_pre_topc(sK6,sK7)
    | spl11_2 ),
    inference(resolution,[],[f229,f119])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v4_pre_topc(X0,sK6)
        | k2_pre_topc(sK6,X0) = X0 )
    | spl11_2 ),
    inference(subsumption_resolution,[],[f228,f76])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK7))
        | ~ v4_pre_topc(X0,sK6)
        | k2_pre_topc(sK6,X0) = X0
        | ~ l1_pre_topc(sK6) )
    | spl11_2 ),
    inference(superposition,[],[f84,f161])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f135,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f78,f132,f128])).

fof(f78,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | v3_tex_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (16894)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (16896)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (16909)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (16902)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16915)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.27/0.52  % (16902)Refutation not found, incomplete strategy% (16902)------------------------------
% 1.27/0.52  % (16902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (16902)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (16902)Memory used [KB]: 6140
% 1.27/0.52  % (16902)Time elapsed: 0.113 s
% 1.27/0.52  % (16902)------------------------------
% 1.27/0.52  % (16902)------------------------------
% 1.27/0.53  % (16892)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.27/0.53  % (16904)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.39/0.54  % (16900)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.54  % (16900)Refutation not found, incomplete strategy% (16900)------------------------------
% 1.39/0.54  % (16900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (16900)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (16900)Memory used [KB]: 10618
% 1.39/0.54  % (16900)Time elapsed: 0.123 s
% 1.39/0.54  % (16900)------------------------------
% 1.39/0.54  % (16900)------------------------------
% 1.39/0.54  % (16897)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.39/0.54  % (16903)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.39/0.54  % (16898)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.39/0.54  % (16905)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.39/0.54  % (16893)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.39/0.54  % (16912)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.39/0.55  % (16890)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.55  % (16889)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.39/0.55  % (16889)Refutation not found, incomplete strategy% (16889)------------------------------
% 1.39/0.55  % (16889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (16889)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (16889)Memory used [KB]: 10618
% 1.39/0.55  % (16889)Time elapsed: 0.108 s
% 1.39/0.55  % (16889)------------------------------
% 1.39/0.55  % (16889)------------------------------
% 1.39/0.55  % (16906)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.39/0.55  % (16895)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.55  % (16907)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.55  % (16895)Refutation not found, incomplete strategy% (16895)------------------------------
% 1.39/0.55  % (16895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (16895)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (16895)Memory used [KB]: 10618
% 1.39/0.55  % (16895)Time elapsed: 0.138 s
% 1.39/0.55  % (16895)------------------------------
% 1.39/0.55  % (16895)------------------------------
% 1.39/0.55  % (16908)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.39/0.56  % (16913)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.39/0.56  % (16915)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f605,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(avatar_sat_refutation,[],[f135,f242,f305,f322,f367,f393,f397,f491,f604])).
% 1.39/0.56  % (16910)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.56  fof(f604,plain,(
% 1.39/0.56    spl11_2 | ~spl11_3 | ~spl11_5),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f603])).
% 1.39/0.56  fof(f603,plain,(
% 1.39/0.56    $false | (spl11_2 | ~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f602,f330])).
% 1.39/0.56  fof(f330,plain,(
% 1.39/0.56    ~v3_tex_2(sK7,sK6) | spl11_2),
% 1.39/0.56    inference(global_subsumption,[],[f79,f134])).
% 1.39/0.56  fof(f134,plain,(
% 1.39/0.56    ~v1_subset_1(sK7,u1_struct_0(sK6)) | spl11_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f132])).
% 1.39/0.56  fof(f132,plain,(
% 1.39/0.56    spl11_2 <=> v1_subset_1(sK7,u1_struct_0(sK6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.39/0.56  fof(f79,plain,(
% 1.39/0.56    v1_subset_1(sK7,u1_struct_0(sK6)) | ~v3_tex_2(sK7,sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    ((v1_subset_1(sK7,u1_struct_0(sK6)) | ~v3_tex_2(sK7,sK6)) & (~v1_subset_1(sK7,u1_struct_0(sK6)) | v3_tex_2(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK6)) | ~v3_tex_2(X1,sK6)) & (~v1_subset_1(X1,u1_struct_0(sK6)) | v3_tex_2(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v1_tdlat_3(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK6)) | ~v3_tex_2(X1,sK6)) & (~v1_subset_1(X1,u1_struct_0(sK6)) | v3_tex_2(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) => ((v1_subset_1(sK7,u1_struct_0(sK6)) | ~v3_tex_2(sK7,sK6)) & (~v1_subset_1(sK7,u1_struct_0(sK6)) | v3_tex_2(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f48])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f18])).
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f17])).
% 1.39/0.56  fof(f17,negated_conjecture,(
% 1.39/0.56    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.39/0.56    inference(negated_conjecture,[],[f16])).
% 1.39/0.56  fof(f16,conjecture,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 1.39/0.56  fof(f602,plain,(
% 1.39/0.56    v3_tex_2(sK7,sK6) | (spl11_2 | ~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f598,f288])).
% 1.39/0.56  fof(f288,plain,(
% 1.39/0.56    v1_tops_1(sK7,sK6) | ~spl11_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f287])).
% 1.39/0.56  fof(f287,plain,(
% 1.39/0.56    spl11_5 <=> v1_tops_1(sK7,sK6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.39/0.56  fof(f598,plain,(
% 1.39/0.56    ~v1_tops_1(sK7,sK6) | v3_tex_2(sK7,sK6) | (spl11_2 | ~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(resolution,[],[f597,f119])).
% 1.39/0.56  fof(f119,plain,(
% 1.39/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(forward_demodulation,[],[f82,f81])).
% 1.39/0.56  fof(f81,plain,(
% 1.39/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.39/0.56  fof(f82,plain,(
% 1.39/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.39/0.56  fof(f597,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v1_tops_1(X0,sK6) | v3_tex_2(X0,sK6)) ) | (spl11_2 | ~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f596,f205])).
% 1.39/0.56  fof(f205,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v2_tex_2(X0,sK6)) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f204,f73])).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    ~v2_struct_0(sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f204,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v2_tex_2(X0,sK6) | v2_struct_0(sK6)) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f203,f75])).
% 1.39/0.56  fof(f75,plain,(
% 1.39/0.56    v1_tdlat_3(sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f203,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v2_tex_2(X0,sK6) | ~v1_tdlat_3(sK6) | v2_struct_0(sK6)) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f201,f76])).
% 1.39/0.56  fof(f76,plain,(
% 1.39/0.56    l1_pre_topc(sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f201,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v2_tex_2(X0,sK6) | ~l1_pre_topc(sK6) | ~v1_tdlat_3(sK6) | v2_struct_0(sK6)) ) | spl11_2),
% 1.39/0.56    inference(superposition,[],[f120,f161])).
% 1.39/0.56  fof(f161,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f158,f134])).
% 1.39/0.56  fof(f158,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | v1_subset_1(sK7,u1_struct_0(sK6))),
% 1.39/0.56    inference(resolution,[],[f111,f77])).
% 1.39/0.56  fof(f77,plain,(
% 1.39/0.56    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f111,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f68])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f35])).
% 1.39/0.56  fof(f35,plain,(
% 1.39/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.39/0.56  fof(f120,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f101,f83])).
% 1.39/0.56  fof(f83,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f20])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.39/0.56  fof(f101,plain,(
% 1.39/0.56    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f14])).
% 1.39/0.56  fof(f14,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.39/0.56  fof(f596,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v2_tex_2(X0,sK6) | ~v1_tops_1(X0,sK6) | v3_tex_2(X0,sK6)) ) | (~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f595,f73])).
% 1.39/0.56  fof(f595,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v2_tex_2(X0,sK6) | ~v1_tops_1(X0,sK6) | v3_tex_2(X0,sK6) | v2_struct_0(sK6)) ) | (~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f594,f74])).
% 1.39/0.56  fof(f74,plain,(
% 1.39/0.56    v2_pre_topc(sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f594,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v2_tex_2(X0,sK6) | ~v1_tops_1(X0,sK6) | v3_tex_2(X0,sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f592,f76])).
% 1.39/0.56  fof(f592,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v2_tex_2(X0,sK6) | ~v1_tops_1(X0,sK6) | v3_tex_2(X0,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(superposition,[],[f102,f499])).
% 1.39/0.56  fof(f499,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | (~spl11_3 | ~spl11_5)),
% 1.39/0.56    inference(forward_demodulation,[],[f498,f237])).
% 1.39/0.56  fof(f237,plain,(
% 1.39/0.56    sK7 = k2_pre_topc(sK6,sK7) | ~spl11_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f235])).
% 1.39/0.56  fof(f235,plain,(
% 1.39/0.56    spl11_3 <=> sK7 = k2_pre_topc(sK6,sK7)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.39/0.56  fof(f498,plain,(
% 1.39/0.56    u1_struct_0(sK6) = k2_pre_topc(sK6,sK7) | ~spl11_5),
% 1.39/0.56    inference(subsumption_resolution,[],[f497,f76])).
% 1.39/0.56  fof(f497,plain,(
% 1.39/0.56    u1_struct_0(sK6) = k2_pre_topc(sK6,sK7) | ~l1_pre_topc(sK6) | ~spl11_5),
% 1.39/0.56    inference(subsumption_resolution,[],[f306,f288])).
% 1.39/0.56  fof(f306,plain,(
% 1.39/0.56    ~v1_tops_1(sK7,sK6) | u1_struct_0(sK6) = k2_pre_topc(sK6,sK7) | ~l1_pre_topc(sK6)),
% 1.39/0.56    inference(resolution,[],[f77,f86])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 1.39/0.56  fof(f102,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 1.39/0.56  fof(f491,plain,(
% 1.39/0.56    ~spl11_2 | ~spl11_6 | ~spl11_8),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f490])).
% 1.39/0.56  fof(f490,plain,(
% 1.39/0.56    $false | (~spl11_2 | ~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(subsumption_resolution,[],[f489,f118])).
% 1.39/0.56  fof(f118,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.39/0.56    inference(backward_demodulation,[],[f80,f81])).
% 1.39/0.56  fof(f80,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.39/0.56  fof(f489,plain,(
% 1.39/0.56    v1_subset_1(sK7,sK7) | (~spl11_2 | ~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(forward_demodulation,[],[f133,f464])).
% 1.39/0.56  fof(f464,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | (~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(subsumption_resolution,[],[f463,f73])).
% 1.39/0.56  fof(f463,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | v2_struct_0(sK6) | (~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(subsumption_resolution,[],[f462,f75])).
% 1.39/0.56  fof(f462,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | ~v1_tdlat_3(sK6) | v2_struct_0(sK6) | (~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(subsumption_resolution,[],[f461,f76])).
% 1.39/0.56  fof(f461,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | ~l1_pre_topc(sK6) | ~v1_tdlat_3(sK6) | v2_struct_0(sK6) | (~spl11_6 | ~spl11_8)),
% 1.39/0.56    inference(subsumption_resolution,[],[f454,f381])).
% 1.39/0.56  fof(f381,plain,(
% 1.39/0.56    sP0(sK7,sK6) | ~spl11_6),
% 1.39/0.56    inference(resolution,[],[f321,f91])).
% 1.39/0.56  fof(f91,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | sP0(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f57])).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.39/0.56    inference(flattening,[],[f56])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 1.39/0.56    inference(nnf_transformation,[],[f40])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.56  fof(f321,plain,(
% 1.39/0.56    sP1(sK6,sK7) | ~spl11_6),
% 1.39/0.56    inference(avatar_component_clause,[],[f319])).
% 1.39/0.56  fof(f319,plain,(
% 1.39/0.56    spl11_6 <=> sP1(sK6,sK7)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.39/0.56  fof(f454,plain,(
% 1.39/0.56    u1_struct_0(sK6) = sK7 | ~sP0(sK7,sK6) | ~l1_pre_topc(sK6) | ~v1_tdlat_3(sK6) | v2_struct_0(sK6) | ~spl11_8),
% 1.39/0.56    inference(resolution,[],[f447,f392])).
% 1.39/0.56  fof(f392,plain,(
% 1.39/0.56    r1_tarski(sK7,u1_struct_0(sK6)) | ~spl11_8),
% 1.39/0.56    inference(avatar_component_clause,[],[f390])).
% 1.39/0.56  fof(f390,plain,(
% 1.39/0.56    spl11_8 <=> r1_tarski(sK7,u1_struct_0(sK6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.39/0.56  fof(f447,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | u1_struct_0(X1) = X0 | ~sP0(X0,X1) | ~l1_pre_topc(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1)) )),
% 1.39/0.56    inference(resolution,[],[f437,f196])).
% 1.39/0.56  fof(f196,plain,(
% 1.39/0.56    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(resolution,[],[f120,f119])).
% 1.39/0.56  fof(f437,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v2_tex_2(u1_struct_0(X1),X1) | ~r1_tarski(X0,u1_struct_0(X1)) | u1_struct_0(X1) = X0 | ~sP0(X0,X1)) )),
% 1.39/0.56    inference(resolution,[],[f93,f119])).
% 1.39/0.56  fof(f93,plain,(
% 1.39/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | X0 = X3 | ~sP0(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f61])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    ! [X0,X1] : ((sP0(X0,X1) | (sK8(X0,X1) != X0 & r1_tarski(X0,sK8(X0,X1)) & v2_tex_2(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK8(X0,X1) != X0 & r1_tarski(X0,sK8(X0,X1)) & v2_tex_2(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.39/0.56    inference(rectify,[],[f58])).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.56  fof(f133,plain,(
% 1.39/0.56    v1_subset_1(sK7,u1_struct_0(sK6)) | ~spl11_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f132])).
% 1.39/0.56  fof(f397,plain,(
% 1.39/0.56    ~spl11_7),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f396])).
% 1.39/0.56  fof(f396,plain,(
% 1.39/0.56    $false | ~spl11_7),
% 1.39/0.56    inference(resolution,[],[f395,f388])).
% 1.39/0.56  fof(f388,plain,(
% 1.39/0.56    sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6)) | ~spl11_7),
% 1.39/0.56    inference(avatar_component_clause,[],[f386])).
% 1.39/0.56  fof(f386,plain,(
% 1.39/0.56    spl11_7 <=> sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.39/0.56  fof(f395,plain,(
% 1.39/0.56    ( ! [X0] : (~sP5(u1_struct_0(sK6),sK7,X0)) )),
% 1.39/0.56    inference(duplicate_literal_removal,[],[f394])).
% 1.39/0.56  fof(f394,plain,(
% 1.39/0.56    ( ! [X0] : (~sP5(u1_struct_0(sK6),sK7,X0) | ~sP5(u1_struct_0(sK6),sK7,X0)) )),
% 1.39/0.56    inference(resolution,[],[f384,f114])).
% 1.39/0.56  fof(f114,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | ~sP5(X0,X1,X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f72])).
% 1.39/0.56  fof(f72,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((~r2_hidden(sK10(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),X2)) | ~sP5(X0,X1,X2))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).
% 1.39/0.56  fof(f71,plain,(
% 1.39/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) => (~r2_hidden(sK10(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),X2)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f70,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) | ~sP5(X0,X1,X2))),
% 1.39/0.56    inference(rectify,[],[f69])).
% 1.39/0.56  fof(f69,plain,(
% 1.39/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP5(X2,X1,X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f46])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP5(X2,X1,X0))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.39/0.56  fof(f384,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(sK10(u1_struct_0(sK6),X0,X1),sK7) | ~sP5(u1_struct_0(sK6),X0,X1)) )),
% 1.39/0.56    inference(resolution,[],[f313,f115])).
% 1.39/0.56  fof(f115,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,X1,X2),X0) | ~sP5(X0,X1,X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f72])).
% 1.39/0.56  fof(f313,plain,(
% 1.39/0.56    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK6)) | ~r2_hidden(X1,sK7)) )),
% 1.39/0.56    inference(resolution,[],[f77,f112])).
% 1.39/0.56  fof(f112,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f36])).
% 1.39/0.56  fof(f36,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.39/0.56  fof(f393,plain,(
% 1.39/0.56    spl11_7 | spl11_8),
% 1.39/0.56    inference(avatar_split_clause,[],[f311,f390,f386])).
% 1.39/0.56  fof(f311,plain,(
% 1.39/0.56    r1_tarski(sK7,u1_struct_0(sK6)) | sP5(u1_struct_0(sK6),sK7,u1_struct_0(sK6))),
% 1.39/0.56    inference(resolution,[],[f77,f248])).
% 1.39/0.56  fof(f248,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0) | sP5(X0,X1,X0)) )),
% 1.39/0.56    inference(resolution,[],[f116,f119])).
% 1.39/0.56  fof(f116,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP5(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | sP5(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(definition_folding,[],[f38,f46])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(flattening,[],[f37])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 1.39/0.56  fof(f367,plain,(
% 1.39/0.56    spl11_2 | ~spl11_3 | spl11_5),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f366])).
% 1.39/0.56  fof(f366,plain,(
% 1.39/0.56    $false | (spl11_2 | ~spl11_3 | spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f365,f119])).
% 1.39/0.56  fof(f365,plain,(
% 1.39/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(sK7)) | (spl11_2 | ~spl11_3 | spl11_5)),
% 1.39/0.56    inference(forward_demodulation,[],[f364,f161])).
% 1.39/0.56  fof(f364,plain,(
% 1.39/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | (spl11_2 | ~spl11_3 | spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f363,f76])).
% 1.39/0.56  fof(f363,plain,(
% 1.39/0.56    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6) | (spl11_2 | ~spl11_3 | spl11_5)),
% 1.39/0.56    inference(subsumption_resolution,[],[f362,f289])).
% 1.39/0.56  fof(f289,plain,(
% 1.39/0.56    ~v1_tops_1(sK7,sK6) | spl11_5),
% 1.39/0.56    inference(avatar_component_clause,[],[f287])).
% 1.39/0.56  fof(f362,plain,(
% 1.39/0.56    v1_tops_1(sK7,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6) | (spl11_2 | ~spl11_3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f361,f161])).
% 1.39/0.56  fof(f361,plain,(
% 1.39/0.56    u1_struct_0(sK6) != sK7 | v1_tops_1(sK7,sK6) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6) | ~spl11_3),
% 1.39/0.56    inference(superposition,[],[f87,f237])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f322,plain,(
% 1.39/0.56    spl11_6 | ~spl11_1),
% 1.39/0.56    inference(avatar_split_clause,[],[f143,f128,f319])).
% 1.39/0.56  fof(f128,plain,(
% 1.39/0.56    spl11_1 <=> v3_tex_2(sK7,sK6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.39/0.56  fof(f143,plain,(
% 1.39/0.56    ~v3_tex_2(sK7,sK6) | sP1(sK6,sK7)),
% 1.39/0.56    inference(resolution,[],[f141,f88])).
% 1.39/0.56  fof(f88,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f55])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 1.39/0.56    inference(rectify,[],[f54])).
% 1.39/0.56  fof(f54,plain,(
% 1.39/0.56    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f41])).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.39/0.56  fof(f141,plain,(
% 1.39/0.56    sP2(sK7,sK6)),
% 1.39/0.56    inference(subsumption_resolution,[],[f138,f76])).
% 1.39/0.56  fof(f138,plain,(
% 1.39/0.56    sP2(sK7,sK6) | ~l1_pre_topc(sK6)),
% 1.39/0.56    inference(resolution,[],[f98,f77])).
% 1.39/0.56  fof(f98,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(definition_folding,[],[f26,f41,f40,f39])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.39/0.56  fof(f305,plain,(
% 1.39/0.56    spl11_2 | spl11_4),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f304])).
% 1.39/0.56  fof(f304,plain,(
% 1.39/0.56    $false | (spl11_2 | spl11_4)),
% 1.39/0.56    inference(subsumption_resolution,[],[f300,f241])).
% 1.39/0.56  fof(f241,plain,(
% 1.39/0.56    ~v4_pre_topc(sK7,sK6) | spl11_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f239])).
% 1.39/0.56  fof(f239,plain,(
% 1.39/0.56    spl11_4 <=> v4_pre_topc(sK7,sK6)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.39/0.56  fof(f300,plain,(
% 1.39/0.56    v4_pre_topc(sK7,sK6) | spl11_2),
% 1.39/0.56    inference(resolution,[],[f299,f119])).
% 1.39/0.56  fof(f299,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v4_pre_topc(X0,sK6)) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f298,f173])).
% 1.39/0.56  fof(f173,plain,(
% 1.39/0.56    ( ! [X0] : (v3_pre_topc(k3_subset_1(sK7,X0),sK6) | ~m1_subset_1(X0,k1_zfmisc_1(sK7))) ) | spl11_2),
% 1.39/0.56    inference(resolution,[],[f170,f109])).
% 1.39/0.56  fof(f109,plain,(
% 1.39/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.39/0.56  fof(f170,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v3_pre_topc(X0,sK6)) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f165,f126])).
% 1.39/0.56  fof(f126,plain,(
% 1.39/0.56    sP3(sK6)),
% 1.39/0.56    inference(subsumption_resolution,[],[f125,f75])).
% 1.39/0.56  fof(f125,plain,(
% 1.39/0.56    ~v1_tdlat_3(sK6) | sP3(sK6)),
% 1.39/0.56    inference(resolution,[],[f123,f103])).
% 1.39/0.56  fof(f103,plain,(
% 1.39/0.56    ( ! [X0] : (~sP4(X0) | ~v1_tdlat_3(X0) | sP3(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f63])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    ! [X0] : (((v1_tdlat_3(X0) | ~sP3(X0)) & (sP3(X0) | ~v1_tdlat_3(X0))) | ~sP4(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ! [X0] : ((v1_tdlat_3(X0) <=> sP3(X0)) | ~sP4(X0))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.39/0.56  fof(f123,plain,(
% 1.39/0.56    sP4(sK6)),
% 1.39/0.56    inference(subsumption_resolution,[],[f122,f76])).
% 1.39/0.56  fof(f122,plain,(
% 1.39/0.56    ~l1_pre_topc(sK6) | sP4(sK6)),
% 1.39/0.56    inference(resolution,[],[f108,f74])).
% 1.39/0.56  fof(f108,plain,(
% 1.39/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP4(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ! [X0] : (sP4(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(definition_folding,[],[f33,f44,f43])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ! [X0] : (sP3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f13])).
% 1.39/0.56  fof(f13,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.39/0.56  fof(f165,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | v3_pre_topc(X0,sK6) | ~sP3(sK6)) ) | spl11_2),
% 1.39/0.56    inference(superposition,[],[f105,f161])).
% 1.39/0.56  fof(f105,plain,(
% 1.39/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~sP3(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f67])).
% 1.39/0.56  fof(f67,plain,(
% 1.39/0.56    ! [X0] : ((sP3(X0) | (~v3_pre_topc(sK9(X0),X0) & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).
% 1.39/0.56  fof(f66,plain,(
% 1.39/0.56    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK9(X0),X0) & m1_subset_1(sK9(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    ! [X0] : ((sP3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0)))),
% 1.39/0.56    inference(rectify,[],[f64])).
% 1.39/0.56  fof(f64,plain,(
% 1.39/0.56    ! [X0] : ((sP3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f43])).
% 1.39/0.56  fof(f298,plain,(
% 1.39/0.56    ( ! [X0] : (~v3_pre_topc(k3_subset_1(sK7,X0),sK6) | v4_pre_topc(X0,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(sK7))) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f295,f76])).
% 1.39/0.56  fof(f295,plain,(
% 1.39/0.56    ( ! [X0] : (~v3_pre_topc(k3_subset_1(sK7,X0),sK6) | v4_pre_topc(X0,sK6) | ~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~l1_pre_topc(sK6)) ) | spl11_2),
% 1.39/0.56    inference(superposition,[],[f100,f161])).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f62])).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f27])).
% 1.39/0.56  fof(f27,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.39/0.56  fof(f242,plain,(
% 1.39/0.56    spl11_3 | ~spl11_4 | spl11_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f230,f132,f239,f235])).
% 1.39/0.56  fof(f230,plain,(
% 1.39/0.56    ~v4_pre_topc(sK7,sK6) | sK7 = k2_pre_topc(sK6,sK7) | spl11_2),
% 1.39/0.56    inference(resolution,[],[f229,f119])).
% 1.39/0.56  fof(f229,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v4_pre_topc(X0,sK6) | k2_pre_topc(sK6,X0) = X0) ) | spl11_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f228,f76])).
% 1.39/0.56  fof(f228,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK7)) | ~v4_pre_topc(X0,sK6) | k2_pre_topc(sK6,X0) = X0 | ~l1_pre_topc(sK6)) ) | spl11_2),
% 1.39/0.56    inference(superposition,[],[f84,f161])).
% 1.39/0.56  fof(f84,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.39/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.39/0.56  fof(f135,plain,(
% 1.39/0.56    spl11_1 | ~spl11_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f78,f132,f128])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ~v1_subset_1(sK7,u1_struct_0(sK6)) | v3_tex_2(sK7,sK6)),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (16915)------------------------------
% 1.39/0.56  % (16915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (16915)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (16915)Memory used [KB]: 11129
% 1.39/0.56  % (16915)Time elapsed: 0.108 s
% 1.39/0.56  % (16915)------------------------------
% 1.39/0.56  % (16915)------------------------------
% 1.39/0.56  % (16880)Success in time 0.2 s
%------------------------------------------------------------------------------
