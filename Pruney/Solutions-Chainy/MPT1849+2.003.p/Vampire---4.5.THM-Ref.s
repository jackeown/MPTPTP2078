%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 167 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  293 ( 575 expanded)
%              Number of equality atoms :   50 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f76,f88,f113,f121,f136,f158,f182,f198,f429])).

fof(f429,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_18
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_18
    | spl5_20 ),
    inference(subsumption_resolution,[],[f427,f197])).

fof(f197,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_20
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f427,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f408,f179])).

fof(f179,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_18
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f408,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f64,f54,f75,f179,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f75,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_6
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f54,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_2
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_4
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f198,plain,
    ( ~ spl5_20
    | spl5_1
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f187,f177,f47,f195])).

fof(f47,plain,
    ( spl5_1
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f187,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))
    | spl5_1
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f49,f179])).

fof(f49,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f182,plain,
    ( spl5_18
    | spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f181,f155,f133,f177])).

fof(f133,plain,
    ( spl5_14
  <=> v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f155,plain,
    ( spl5_16
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f181,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f175,f135])).

fof(f135,plain,
    ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f175,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl5_16 ),
    inference(resolution,[],[f157,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f157,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl5_16
    | spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f153,f118,f108,f155])).

fof(f108,plain,
    ( spl5_11
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f118,plain,
    ( spl5_12
  <=> u1_struct_0(sK3) = sK4(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f153,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f148,f120])).

fof(f120,plain,
    ( u1_struct_0(sK3) = sK4(sK2,sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f148,plain,
    ( m1_subset_1(sK4(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f110,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v1_subset_1(sK4(X0,X1),u1_struct_0(X0))
          & u1_struct_0(X1) = sK4(X0,X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK4(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v1_subset_1(X3,u1_struct_0(X0))
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v1_subset_1(X2,u1_struct_0(X0))
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v1_subset_1(X2,u1_struct_0(X0))
            | u1_struct_0(X1) != X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v1_subset_1(X2,u1_struct_0(X0))
          | u1_struct_0(X1) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f110,plain,
    ( ~ sP0(sK2,sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f136,plain,
    ( ~ spl5_14
    | spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f131,f118,f108,f133])).

fof(f131,plain,
    ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f128,f120])).

fof(f128,plain,
    ( ~ v1_subset_1(sK4(sK2,sK3),u1_struct_0(sK2))
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f110,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,
    ( spl5_12
    | spl5_11 ),
    inference(avatar_split_clause,[],[f116,f108,f118])).

fof(f116,plain,
    ( u1_struct_0(sK3) = sK4(sK2,sK3)
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f110,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK4(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f113,plain,
    ( ~ spl5_11
    | spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f112,f85,f57,f108])).

fof(f57,plain,
    ( spl5_3
  <=> v1_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f85,plain,
    ( spl5_8
  <=> sP1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f112,plain,
    ( ~ sP0(sK2,sK3)
    | spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f105,f59])).

fof(f59,plain,
    ( ~ v1_tex_2(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f105,plain,
    ( ~ sP0(sK2,sK3)
    | v1_tex_2(sK3,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f35,f87])).

fof(f87,plain,
    ( sP1(sK3,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v1_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( ( v1_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ( v1_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f77,f62,f52,f85])).

fof(f77,plain,
    ( sP1(sK3,sK2)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f64,f54,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f16,f15])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f76,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f71,f62,f73])).

fof(f71,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f64,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_pre_topc(sK3,sK2)
    & ~ v1_tex_2(sK3,sK2)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          & m1_pre_topc(X1,sK2)
          & ~ v1_tex_2(X1,sK2) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_pre_topc(X1,sK2)
        & ~ v1_tex_2(X1,sK2) )
   => ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      & m1_pre_topc(sK3,sK2)
      & ~ v1_tex_2(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(f60,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ~ v1_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f47])).

fof(f32,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (15050)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (15050)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f76,f88,f113,f121,f136,f158,f182,f198,f429])).
% 0.21/0.45  fof(f429,plain,(
% 0.21/0.45    ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_18 | spl5_20),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.45  fof(f428,plain,(
% 0.21/0.45    $false | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_18 | spl5_20)),
% 0.21/0.45    inference(subsumption_resolution,[],[f427,f197])).
% 0.21/0.45  fof(f197,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) | spl5_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f195])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    spl5_20 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.45  fof(f427,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_18)),
% 0.21/0.45    inference(forward_demodulation,[],[f408,f179])).
% 0.21/0.45  fof(f179,plain,(
% 0.21/0.45    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl5_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f177])).
% 0.21/0.45  fof(f177,plain,(
% 0.21/0.45    spl5_18 <=> u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.45  fof(f408,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_18)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f54,f75,f179,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    m1_pre_topc(sK2,sK2) | ~spl5_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl5_6 <=> m1_pre_topc(sK2,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    m1_pre_topc(sK3,sK2) | ~spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl5_2 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    l1_pre_topc(sK2) | ~spl5_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl5_4 <=> l1_pre_topc(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    ~spl5_20 | spl5_1 | ~spl5_18),
% 0.21/0.45    inference(avatar_split_clause,[],[f187,f177,f47,f195])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl5_1 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f187,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK3)) | (spl5_1 | ~spl5_18)),
% 0.21/0.45    inference(backward_demodulation,[],[f49,f179])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | spl5_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    spl5_18 | spl5_14 | ~spl5_16),
% 0.21/0.45    inference(avatar_split_clause,[],[f181,f155,f133,f177])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    spl5_14 <=> v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    spl5_16 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    u1_struct_0(sK2) = u1_struct_0(sK3) | (spl5_14 | ~spl5_16)),
% 0.21/0.45    inference(subsumption_resolution,[],[f175,f135])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    ~v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2)) | spl5_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f133])).
% 0.21/0.45  fof(f175,plain,(
% 0.21/0.45    u1_struct_0(sK2) = u1_struct_0(sK3) | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl5_16),
% 0.21/0.45    inference(resolution,[],[f157,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f155])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    spl5_16 | spl5_11 | ~spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f153,f118,f108,f155])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    spl5_11 <=> sP0(sK2,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    spl5_12 <=> u1_struct_0(sK3) = sK4(sK2,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl5_11 | ~spl5_12)),
% 0.21/0.45    inference(forward_demodulation,[],[f148,f120])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    u1_struct_0(sK3) = sK4(sK2,sK3) | ~spl5_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f118])).
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    m1_subset_1(sK4(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | spl5_11),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f110,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : ((sP0(X0,X1) | (~v1_subset_1(sK4(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK4(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ~sP0(sK2,sK3) | spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f108])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    ~spl5_14 | spl5_11 | ~spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f131,f118,f108,f133])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ~v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2)) | (spl5_11 | ~spl5_12)),
% 0.21/0.45    inference(forward_demodulation,[],[f128,f120])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ~v1_subset_1(sK4(sK2,sK3),u1_struct_0(sK2)) | spl5_11),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f110,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | sP0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    spl5_12 | spl5_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f116,f108,f118])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    u1_struct_0(sK3) = sK4(sK2,sK3) | spl5_11),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f110,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (u1_struct_0(X1) = sK4(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ~spl5_11 | spl5_3 | ~spl5_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f112,f85,f57,f108])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl5_3 <=> v1_tex_2(sK3,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl5_8 <=> sP1(sK3,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ~sP0(sK2,sK3) | (spl5_3 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f105,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~v1_tex_2(sK3,sK2) | spl5_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f57])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    ~sP0(sK2,sK3) | v1_tex_2(sK3,sK2) | ~spl5_8),
% 0.21/0.45    inference(resolution,[],[f35,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    sP1(sK3,sK2) | ~spl5_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v1_tex_2(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (((v1_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v1_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.45    inference(rectify,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X1,X0] : (((v1_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v1_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X1,X0] : ((v1_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl5_8 | ~spl5_2 | ~spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f77,f62,f52,f85])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    sP1(sK3,sK2) | (~spl5_2 | ~spl5_4)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f54,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(definition_folding,[],[f11,f16,f15])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl5_6 | ~spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f71,f62,f73])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    m1_pre_topc(sK2,sK2) | ~spl5_4),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f64,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f62])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    l1_pre_topc(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK2) & ~v1_tex_2(sK3,sK2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f19,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(X1,sK2) & ~v1_tex_2(X1,sK2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(X1,sK2) & ~v1_tex_2(X1,sK2)) => (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK2) & ~v1_tex_2(sK3,sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & (m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ~spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ~v1_tex_2(sK3,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f52])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    m1_pre_topc(sK3,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f47])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (15050)------------------------------
% 0.21/0.45  % (15050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (15050)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (15050)Memory used [KB]: 10874
% 0.21/0.45  % (15050)Time elapsed: 0.036 s
% 0.21/0.45  % (15050)------------------------------
% 0.21/0.45  % (15050)------------------------------
% 0.21/0.45  % (15033)Success in time 0.09 s
%------------------------------------------------------------------------------
