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
% DateTime   : Thu Dec  3 13:21:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 (1136 expanded)
%              Number of leaves         :   20 ( 333 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (9633 expanded)
%              Number of equality atoms :   15 ( 137 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f110,f124,f132,f146,f171,f179,f196,f206])).

fof(f206,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f91,f86,f109,f89,f117,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

fof(f117,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_4
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f89,plain,(
    v2_pre_topc(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f48,f87,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f87,plain,(
    m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_3
  <=> v7_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,(
    ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    l1_pre_topc(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f87,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f196,plain,
    ( ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f48,f45,f50,f87,f76,f129])).

fof(f129,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7)))
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(sK2(sK0,sK1),X7)
        | ~ v2_tex_2(sK1,X7) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_6
  <=> ! [X7] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ v2_tex_2(sK1,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f179,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f91,f86,f89,f116,f90,f108,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f108,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f90,plain,(
    v2_tdlat_3(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f87,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f47,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f171,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f170,f107,f79])).

fof(f79,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f170,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(global_subsumption,[],[f92,f98])).

fof(f98,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f70,f88])).

fof(f88,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f92,plain,(
    l1_struct_0(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f146,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f48,f45,f77,f87,f50,f120])).

fof(f120,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(sK2(sK0,sK1),X3)
        | v2_tex_2(sK1,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_5
  <=> ! [X3] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X3)
        | v2_struct_0(X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | v2_tex_2(sK1,X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f77,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f132,plain,
    ( spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f131,f128,f115])).

fof(f131,plain,(
    ! [X8] :
      ( ~ m1_pre_topc(sK2(sK0,sK1),X8)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X8)))
      | v1_tdlat_3(sK2(sK0,sK1))
      | ~ l1_pre_topc(X8)
      | ~ v2_tex_2(sK1,X8)
      | v2_struct_0(X8) ) ),
    inference(global_subsumption,[],[f126])).

fof(f126,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(sK2(sK0,sK1),X7)
      | ~ v2_tex_2(sK1,X7)
      | v1_tdlat_3(sK2(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(global_subsumption,[],[f86,f103])).

fof(f103,plain,(
    ! [X7] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7)))
      | v1_tdlat_3(sK2(sK0,sK1))
      | ~ v2_tex_2(sK1,X7)
      | ~ m1_pre_topc(sK2(sK0,sK1),X7)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(superposition,[],[f73,f88])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f124,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f123,f115,f119])).

fof(f123,plain,(
    ! [X5] :
      ( ~ v1_tdlat_3(sK2(sK0,sK1))
      | v2_struct_0(X5)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | v2_tex_2(sK1,X5)
      | ~ m1_pre_topc(sK2(sK0,sK1),X5) ) ),
    inference(global_subsumption,[],[f113])).

fof(f113,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK2(sK0,sK1),X3)
      | ~ l1_pre_topc(X3)
      | v2_tex_2(sK1,X3)
      | ~ v1_tdlat_3(sK2(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
      | v2_struct_0(X3) ) ),
    inference(global_subsumption,[],[f86,f99])).

fof(f99,plain,(
    ! [X3] :
      ( v2_tex_2(sK1,X3)
      | ~ v1_tdlat_3(sK2(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(sK2(sK0,sK1),X3)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f72,f88])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f105,f107,f79])).

fof(f105,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(global_subsumption,[],[f92,f94])).

fof(f94,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f63,f88])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f83,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f79,f75])).

fof(f51,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f79,f75])).

fof(f52,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (6222)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (6220)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (6228)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (6233)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (6225)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (6230)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (6225)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f82,f83,f110,f124,f132,f146,f171,f179,f196,f206])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ~spl3_3 | spl3_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    $false | (~spl3_3 | spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f91,f86,f109,f89,f117,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ~v1_tdlat_3(sK2(sK0,sK1)) | spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl3_4 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    v2_pre_topc(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f46,f48,f87,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f12])).
% 0.22/0.51  fof(f12,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    v7_struct_0(sK2(sK0,sK1)) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl3_3 <=> v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f48,f87,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f195])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    $false | (~spl3_1 | ~spl3_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f48,f45,f50,f87,f76,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X7] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7))) | v2_struct_0(X7) | ~l1_pre_topc(X7) | ~m1_pre_topc(sK2(sK0,sK1),X7) | ~v2_tex_2(sK1,X7)) ) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl3_6 <=> ! [X7] : (~m1_pre_topc(sK2(sK0,sK1),X7) | v2_struct_0(X7) | ~l1_pre_topc(X7) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7))) | ~v2_tex_2(sK1,X7))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl3_3 | ~spl3_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    $false | (spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f91,f86,f89,f116,f90,f108,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~v7_struct_0(sK2(sK0,sK1)) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f107])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    v2_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f87,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v2_tdlat_3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    v1_tdlat_3(sK2(sK0,sK1)) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f115])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    spl3_2 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f170,f107,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.51    inference(global_subsumption,[],[f92,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    inference(superposition,[],[f70,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f45,f48,f49,f50,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f91,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl3_1 | ~spl3_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    $false | (spl3_1 | ~spl3_5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f48,f45,f77,f87,f50,f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(X3) | ~m1_pre_topc(sK2(sK0,sK1),X3) | v2_tex_2(sK1,X3) | ~l1_pre_topc(X3)) ) | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_5 <=> ! [X3] : (~m1_pre_topc(sK2(sK0,sK1),X3) | v2_struct_0(X3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | v2_tex_2(sK1,X3) | ~l1_pre_topc(X3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl3_4 | spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f131,f128,f115])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X8] : (~m1_pre_topc(sK2(sK0,sK1),X8) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X8))) | v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(X8) | ~v2_tex_2(sK1,X8) | v2_struct_0(X8)) )),
% 0.22/0.51    inference(global_subsumption,[],[f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X7] : (~m1_pre_topc(sK2(sK0,sK1),X7) | ~v2_tex_2(sK1,X7) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7))) | ~l1_pre_topc(X7) | v2_struct_0(X7)) )),
% 0.22/0.51    inference(global_subsumption,[],[f86,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X7] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X7))) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,X7) | ~m1_pre_topc(sK2(sK0,sK1),X7) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X7) | v2_struct_0(X7)) )),
% 0.22/0.51    inference(superposition,[],[f73,f88])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl3_5 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f123,f115,f119])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X5] : (~v1_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(X5) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | v2_tex_2(sK1,X5) | ~m1_pre_topc(sK2(sK0,sK1),X5)) )),
% 0.22/0.52    inference(global_subsumption,[],[f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_pre_topc(sK2(sK0,sK1),X3) | ~l1_pre_topc(X3) | v2_tex_2(sK1,X3) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(X3)) )),
% 0.22/0.52    inference(global_subsumption,[],[f86,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X3] : (v2_tex_2(sK1,X3) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(sK2(sK0,sK1),X3) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.22/0.52    inference(superposition,[],[f72,f88])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ~spl3_2 | spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f107,f79])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | ~v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(global_subsumption,[],[f92,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f63,f88])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl3_1 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f51,f79,f75])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f79,f75])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6225)------------------------------
% 0.22/0.52  % (6225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6225)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6225)Memory used [KB]: 10746
% 0.22/0.52  % (6225)Time elapsed: 0.064 s
% 0.22/0.52  % (6225)------------------------------
% 0.22/0.52  % (6225)------------------------------
% 0.22/0.52  % (6213)Success in time 0.148 s
%------------------------------------------------------------------------------
