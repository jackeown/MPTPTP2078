%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 325 expanded)
%              Number of leaves         :   29 ( 152 expanded)
%              Depth                    :    8
%              Number of atoms          :  636 (2307 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f300,f308,f329,f333,f342,f346,f352,f357,f362,f426,f427,f428,f497,f502,f507,f686,f687,f814,f856])).

fof(f856,plain,
    ( ~ spl4_41
    | ~ spl4_48
    | ~ spl4_49
    | ~ spl4_50
    | spl4_65
    | ~ spl4_68
    | spl4_114 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | ~ spl4_41
    | ~ spl4_48
    | ~ spl4_49
    | ~ spl4_50
    | spl4_65
    | ~ spl4_68
    | spl4_114 ),
    inference(unit_resulting_resolution,[],[f31,f32,f34,f495,f380,f375,f370,f813,f511,f460])).

fof(f460,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK2(X0,X1),sK0)
        | m1_pre_topc(sK1,sK2(X0,X1))
        | ~ v3_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_xboole_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(u1_struct_0(sK1),X1)
        | v2_struct_0(X0) )
    | ~ spl4_41 ),
    inference(superposition,[],[f307,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & v4_tex_2(sK2(X0,X1),X0)
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & v4_tex_2(X2,X0)
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & v4_tex_2(sK2(X0,X1),X0)
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & v4_tex_2(X2,X0)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f307,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(sK1,X1) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl4_41
  <=> ! [X1] :
        ( m1_pre_topc(sK1,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f511,plain,
    ( m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl4_68
  <=> m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f813,plain,
    ( ~ m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl4_114 ),
    inference(avatar_component_clause,[],[f811])).

fof(f811,plain,
    ( spl4_114
  <=> m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f370,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl4_48
  <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f375,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl4_49
  <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f380,plain,
    ( v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl4_50
  <=> v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f495,plain,
    ( ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl4_65
  <=> v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X2] :
        ( ~ v4_tex_2(X2,sK0)
        | ~ m1_pre_topc(sK1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & m1_pre_topc(sK1,sK0)
    & v1_tdlat_3(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X1,X2)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,sK0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,sK0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v4_tex_2(X2,sK0)
            | ~ m1_pre_topc(X1,X2)
            | ~ m1_pre_topc(X2,sK0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & v1_tdlat_3(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v4_tex_2(X2,sK0)
          | ~ m1_pre_topc(sK1,X2)
          | ~ m1_pre_topc(X2,sK0)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & v1_tdlat_3(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f814,plain,
    ( spl4_66
    | ~ spl4_67
    | ~ spl4_68
    | ~ spl4_114
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f809,f514,f811,f509,f504,f499])).

fof(f499,plain,
    ( spl4_66
  <=> v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f504,plain,
    ( spl4_67
  <=> v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f514,plain,
    ( spl4_69
  <=> v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f809,plain,
    ( ~ m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl4_69 ),
    inference(resolution,[],[f516,f38])).

fof(f38,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f516,plain,
    ( v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f514])).

fof(f687,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | spl4_65
    | ~ spl4_50
    | spl4_69
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f680,f368,f514,f378,f493,f73,f69,f148])).

fof(f148,plain,
    ( spl4_18
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f69,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f680,plain,
    ( v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_48 ),
    inference(resolution,[],[f370,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_tex_2(sK2(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f686,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | spl4_65
    | ~ spl4_50
    | spl4_68
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f679,f368,f509,f378,f493,f73,f69,f148])).

fof(f679,plain,
    ( m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_48 ),
    inference(resolution,[],[f370,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f507,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | spl4_65
    | ~ spl4_48
    | spl4_67
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f488,f378,f504,f368,f493,f73,f69,f148])).

fof(f488,plain,
    ( v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_50 ),
    inference(resolution,[],[f380,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK2(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f502,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | spl4_65
    | ~ spl4_48
    | ~ spl4_66
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f487,f378,f499,f368,f493,f73,f69,f148])).

fof(f487,plain,
    ( ~ v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_50 ),
    inference(resolution,[],[f380,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f497,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_65
    | ~ spl4_48
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f486,f378,f368,f493,f73,f69,f148])).

fof(f486,plain,
    ( ~ m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_50 ),
    inference(resolution,[],[f380,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f428,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_2
    | ~ spl4_46
    | spl4_50
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f391,f297,f378,f326,f73,f97,f69,f148])).

fof(f97,plain,
    ( spl4_8
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f326,plain,
    ( spl4_46
  <=> v2_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f297,plain,
    ( spl4_39
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f391,plain,
    ( v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_39 ),
    inference(resolution,[],[f299,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK3(X0,X1),X0)
            & r1_tarski(X1,sK3(X0,X1))
            & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK3(X0,X1),X0)
        & r1_tarski(X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f299,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f297])).

fof(f427,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_2
    | ~ spl4_46
    | spl4_49
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f390,f297,f373,f326,f73,f97,f69,f148])).

fof(f390,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_39 ),
    inference(resolution,[],[f299,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f426,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_2
    | ~ spl4_46
    | spl4_48
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f389,f297,f368,f326,f73,f97,f69,f148])).

fof(f389,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_39 ),
    inference(resolution,[],[f299,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f362,plain,(
    ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f35,f286])).

fof(f286,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_38
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f357,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f36,f269])).

fof(f269,plain,
    ( ~ v1_tdlat_3(sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl4_34
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f36,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f352,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f31,f150])).

fof(f150,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f346,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f33,f99])).

fof(f99,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f33,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f342,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f34,f75])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f333,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f32,f71])).

fof(f71,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f329,plain,
    ( spl4_18
    | ~ spl4_2
    | spl4_38
    | ~ spl4_39
    | ~ spl4_34
    | spl4_46 ),
    inference(avatar_split_clause,[],[f294,f326,f267,f297,f284,f73,f148])).

fof(f294,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ v1_tdlat_3(sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f308,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_41 ),
    inference(avatar_split_clause,[],[f290,f306,f73,f69])).

fof(f290,plain,(
    ! [X1] :
      ( m1_pre_topc(sK1,X1)
      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f300,plain,
    ( ~ spl4_2
    | spl4_39 ),
    inference(avatar_split_clause,[],[f288,f297,f73])).

fof(f288,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (8226)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (8218)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (8212)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (8218)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f861,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f300,f308,f329,f333,f342,f346,f352,f357,f362,f426,f427,f428,f497,f502,f507,f686,f687,f814,f856])).
% 0.20/0.50  fof(f856,plain,(
% 0.20/0.50    ~spl4_41 | ~spl4_48 | ~spl4_49 | ~spl4_50 | spl4_65 | ~spl4_68 | spl4_114),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f854])).
% 0.20/0.50  fof(f854,plain,(
% 0.20/0.50    $false | (~spl4_41 | ~spl4_48 | ~spl4_49 | ~spl4_50 | spl4_65 | ~spl4_68 | spl4_114)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f31,f32,f34,f495,f380,f375,f370,f813,f511,f460])).
% 0.20/0.50  fof(f460,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK2(X0,X1),sK0) | m1_pre_topc(sK1,sK2(X0,X1)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~r1_tarski(u1_struct_0(sK1),X1) | v2_struct_0(X0)) ) | ~spl4_41),
% 0.20/0.50    inference(superposition,[],[f307,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & v4_tex_2(sK2(X0,X1),X0) & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & v4_tex_2(X2,X0) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & v4_tex_2(sK2(X0,X1),X0) & m1_pre_topc(sK2(X0,X1),X0) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & v4_tex_2(X2,X0) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((? [X2] : ((u1_struct_0(X2) = X1 & v4_tex_2(X2,X0)) & (m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v3_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(sK1,X1)) ) | ~spl4_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f306])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    spl4_41 <=> ! [X1] : (m1_pre_topc(sK1,X1) | ~m1_pre_topc(X1,sK0) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.20/0.50  fof(f511,plain,(
% 0.20/0.50    m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~spl4_68),
% 0.20/0.50    inference(avatar_component_clause,[],[f509])).
% 0.20/0.50  fof(f509,plain,(
% 0.20/0.50    spl4_68 <=> m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.20/0.50  fof(f813,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | spl4_114),
% 0.20/0.50    inference(avatar_component_clause,[],[f811])).
% 0.20/0.50  fof(f811,plain,(
% 0.20/0.50    spl4_114 <=> m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).
% 0.20/0.50  fof(f370,plain,(
% 0.20/0.50    m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_48),
% 0.20/0.50    inference(avatar_component_clause,[],[f368])).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    spl4_48 <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | ~spl4_49),
% 0.20/0.50    inference(avatar_component_clause,[],[f373])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    spl4_49 <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | ~spl4_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f378])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    spl4_50 <=> v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.20/0.50  fof(f495,plain,(
% 0.20/0.50    ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | spl4_65),
% 0.20/0.50    inference(avatar_component_clause,[],[f493])).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    spl4_65 <=> v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    (! [X2] : (~v4_tex_2(X2,sK0) | ~m1_pre_topc(sK1,X2) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & v1_tdlat_3(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f23,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (~v4_tex_2(X2,sK0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X1] : (! [X2] : (~v4_tex_2(X2,sK0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v4_tex_2(X2,sK0) | ~m1_pre_topc(sK1,X2) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & v1_tdlat_3(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f814,plain,(
% 0.20/0.50    spl4_66 | ~spl4_67 | ~spl4_68 | ~spl4_114 | ~spl4_69),
% 0.20/0.50    inference(avatar_split_clause,[],[f809,f514,f811,f509,f504,f499])).
% 0.20/0.50  fof(f499,plain,(
% 0.20/0.50    spl4_66 <=> v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    spl4_67 <=> v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.20/0.50  fof(f514,plain,(
% 0.20/0.50    spl4_69 <=> v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.20/0.50  fof(f809,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~spl4_69),
% 0.20/0.50    inference(resolution,[],[f516,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2] : (~v4_tex_2(X2,sK0) | ~m1_pre_topc(sK1,X2) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f516,plain,(
% 0.20/0.50    v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~spl4_69),
% 0.20/0.50    inference(avatar_component_clause,[],[f514])).
% 0.20/0.50  fof(f687,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_2 | spl4_65 | ~spl4_50 | spl4_69 | ~spl4_48),
% 0.20/0.50    inference(avatar_split_clause,[],[f680,f368,f514,f378,f493,f73,f69,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl4_18 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl4_1 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl4_2 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f680,plain,(
% 0.20/0.50    v4_tex_2(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_48),
% 0.20/0.50    inference(resolution,[],[f370,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v4_tex_2(sK2(X0,X1),X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f686,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_2 | spl4_65 | ~spl4_50 | spl4_68 | ~spl4_48),
% 0.20/0.50    inference(avatar_split_clause,[],[f679,f368,f509,f378,f493,f73,f69,f148])).
% 0.20/0.50  fof(f679,plain,(
% 0.20/0.50    m1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) | ~v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_48),
% 0.20/0.50    inference(resolution,[],[f370,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f507,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_2 | spl4_65 | ~spl4_48 | spl4_67 | ~spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f488,f378,f504,f368,f493,f73,f69,f148])).
% 0.20/0.50  fof(f488,plain,(
% 0.20/0.50    v1_pre_topc(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_50),
% 0.20/0.50    inference(resolution,[],[f380,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_pre_topc(sK2(X0,X1)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f502,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_2 | spl4_65 | ~spl4_48 | ~spl4_66 | ~spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f487,f378,f499,f368,f493,f73,f69,f148])).
% 0.20/0.50  fof(f487,plain,(
% 0.20/0.50    ~v2_struct_0(sK2(sK0,sK3(sK0,u1_struct_0(sK1)))) | ~m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_50),
% 0.20/0.50    inference(resolution,[],[f380,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f497,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_2 | ~spl4_65 | ~spl4_48 | ~spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f486,f378,f368,f493,f73,f69,f148])).
% 0.20/0.50  fof(f486,plain,(
% 0.20/0.50    ~m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_50),
% 0.20/0.50    inference(resolution,[],[f380,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_8 | ~spl4_2 | ~spl4_46 | spl4_50 | ~spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f391,f297,f378,f326,f73,f97,f69,f148])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl4_8 <=> v3_tdlat_3(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    spl4_46 <=> v2_tex_2(u1_struct_0(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl4_39 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    v3_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_39),
% 0.20/0.50    inference(resolution,[],[f299,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v3_tex_2(sK3(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tex_2(sK3(X0,X1),X0) & r1_tarski(X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK3(X0,X1),X0) & r1_tarski(X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f297])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_8 | ~spl4_2 | ~spl4_46 | spl4_49 | ~spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f390,f297,f373,f326,f73,f97,f69,f148])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_39),
% 0.20/0.50    inference(resolution,[],[f299,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    spl4_18 | ~spl4_1 | ~spl4_8 | ~spl4_2 | ~spl4_46 | spl4_48 | ~spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f389,f297,f368,f326,f73,f97,f69,f148])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_39),
% 0.20/0.50    inference(resolution,[],[f299,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    ~spl4_38),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f359])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    $false | ~spl4_38),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f35,f286])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~spl4_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f284])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    spl4_38 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    spl4_34),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.50  fof(f353,plain,(
% 0.20/0.50    $false | spl4_34),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f36,f269])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ~v1_tdlat_3(sK1) | spl4_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    spl4_34 <=> v1_tdlat_3(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    v1_tdlat_3(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    ~spl4_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f349])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    $false | ~spl4_18),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f31,f150])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~spl4_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f148])).
% 0.20/0.50  fof(f346,plain,(
% 0.20/0.50    spl4_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f343])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    $false | spl4_8),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f33,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~v3_tdlat_3(sK0) | spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v3_tdlat_3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f339])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    $false | spl4_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl4_1),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f330])).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    $false | spl4_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f32,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f69])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    spl4_18 | ~spl4_2 | spl4_38 | ~spl4_39 | ~spl4_34 | spl4_46),
% 0.20/0.50    inference(avatar_split_clause,[],[f294,f326,f267,f297,f284,f73,f148])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    v2_tex_2(u1_struct_0(sK1),sK0) | ~v1_tdlat_3(sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f37,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    ~spl4_1 | ~spl4_2 | spl4_41),
% 0.20/0.50    inference(avatar_split_clause,[],[f290,f306,f73,f69])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    ( ! [X1] : (m1_pre_topc(sK1,X1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f37,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    ~spl4_2 | spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f288,f297,f73])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f37,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (8218)------------------------------
% 0.20/0.50  % (8218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8218)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (8218)Memory used [KB]: 6652
% 0.20/0.50  % (8218)Time elapsed: 0.068 s
% 0.20/0.50  % (8218)------------------------------
% 0.20/0.50  % (8218)------------------------------
% 0.20/0.50  % (8207)Success in time 0.145 s
%------------------------------------------------------------------------------
