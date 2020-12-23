%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 230 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 ( 987 expanded)
%              Number of equality atoms :   53 ( 166 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f71,f78,f102,f109,f128,f141,f158,f196,f223,f232])).

fof(f232,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_26
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f230,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f229,f45])).

fof(f45,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f229,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f228,f55])).

fof(f55,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_4
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f228,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f226,f195])).

fof(f195,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_26
  <=> v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f226,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f222,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f222,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_28
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f223,plain,
    ( spl4_28
    | ~ spl4_7
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f178,f156,f138,f68,f220])).

fof(f68,plain,
    ( spl4_7
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f138,plain,
    ( spl4_17
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f156,plain,
    ( spl4_20
  <=> ! [X3,X2] :
        ( u1_struct_0(sK1) = X2
        | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f178,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f140,f173])).

fof(f173,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(superposition,[],[f157,f70])).

fof(f70,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK1) = X2 )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f140,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f196,plain,
    ( ~ spl4_26
    | ~ spl4_7
    | spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f179,f156,f125,f68,f193])).

fof(f125,plain,
    ( spl4_14
  <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f179,plain,
    ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_7
    | spl4_14
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f127,f173])).

fof(f127,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f158,plain,
    ( spl4_20
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f111,f75,f156])).

fof(f75,plain,
    ( spl4_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f111,plain,
    ( ! [X2,X3] :
        ( u1_struct_0(sK1) = X2
        | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f89,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f141,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f117,f106,f58,f48,f38,f138])).

fof(f48,plain,
    ( spl4_3
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( spl4_5
  <=> v1_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f106,plain,
    ( spl4_13
  <=> u1_struct_0(sK2) = sK3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f117,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f50,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f115,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f113,f60])).

fof(f60,plain,
    ( ~ v1_tex_2(sK2,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f113,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(superposition,[],[f31,f108])).

fof(f108,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f128,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f120,f106,f58,f48,f38,f125])).

fof(f120,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f114,f60])).

fof(f114,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13 ),
    inference(superposition,[],[f33,f108])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f104,f100,f58,f48,f106])).

fof(f100,plain,
    ( spl4_12
  <=> ! [X0] :
        ( u1_struct_0(X0) = sK3(sK0,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f104,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f103,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | u1_struct_0(sK2) = sK3(sK0,sK2)
    | spl4_5
    | ~ spl4_12 ),
    inference(resolution,[],[f101,f60])).

fof(f101,plain,
    ( ! [X0] :
        ( v1_tex_2(X0,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(X0) = sK3(sK0,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl4_12
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f79,f38,f100])).

fof(f79,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = sK3(sK0,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_tex_2(X0,sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f32,f40])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f72,f64,f43,f75])).

fof(f64,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f72,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f66,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f62,f38,f64])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f29,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

% (2759)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f61,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (2761)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (2761)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (2771)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (2779)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (2763)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f71,f78,f102,f109,f128,f141,f158,f196,f223,f232])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_26 | ~spl4_28),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    $false | (~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_26 | ~spl4_28)),
% 0.20/0.53    inference(subsumption_resolution,[],[f230,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    spl4_1 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | (~spl4_2 | ~spl4_4 | spl4_26 | ~spl4_28)),
% 0.20/0.53    inference(subsumption_resolution,[],[f229,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK0) | ~spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    spl4_2 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_4 | spl4_26 | ~spl4_28)),
% 0.20/0.53    inference(subsumption_resolution,[],[f228,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    v1_tex_2(sK1,sK0) | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    spl4_4 <=> v1_tex_2(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl4_26 | ~spl4_28)),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f195])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f193])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl4_26 <=> v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_28),
% 0.20/0.53    inference(resolution,[],[f222,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(rectify,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f220])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    spl4_28 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    spl4_28 | ~spl4_7 | ~spl4_17 | ~spl4_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f178,f156,f138,f68,f220])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl4_7 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    spl4_17 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    spl4_20 <=> ! [X3,X2] : (u1_struct_0(sK1) = X2 | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_7 | ~spl4_17 | ~spl4_20)),
% 0.20/0.53    inference(backward_demodulation,[],[f140,f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    u1_struct_0(sK1) = u1_struct_0(sK2) | (~spl4_7 | ~spl4_20)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK2) | (~spl4_7 | ~spl4_20)),
% 0.20/0.53    inference(superposition,[],[f157,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f68])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK1) = X2) ) | ~spl4_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f156])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f138])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ~spl4_26 | ~spl4_7 | spl4_14 | ~spl4_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f179,f156,f125,f68,f193])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl4_14 <=> v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl4_7 | spl4_14 | ~spl4_20)),
% 0.20/0.53    inference(backward_demodulation,[],[f127,f173])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | spl4_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f125])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    spl4_20 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f111,f75,f156])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    spl4_8 <=> l1_pre_topc(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X2,X3] : (u1_struct_0(sK1) = X2 | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) | ~spl4_8),
% 0.20/0.53    inference(resolution,[],[f89,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    l1_pre_topc(sK1) | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f75])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 0.20/0.53    inference(resolution,[],[f34,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    spl4_17 | ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f117,f106,f58,f48,f38,f138])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    spl4_3 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    spl4_5 <=> v1_tex_2(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl4_13 <=> u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f116,f40])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f115,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK0) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f48])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f113,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ~v1_tex_2(sK2,sK0) | spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f58])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl4_13),
% 0.20/0.53    inference(superposition,[],[f31,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    u1_struct_0(sK2) = sK3(sK0,sK2) | ~spl4_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ~spl4_14 | ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f120,f106,f58,f48,f38,f125])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f119,f40])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl4_3 | spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f118,f50])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (spl4_5 | ~spl4_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f114,f60])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~spl4_13),
% 0.20/0.53    inference(superposition,[],[f33,f108])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl4_13 | ~spl4_3 | spl4_5 | ~spl4_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f104,f100,f58,f48,f106])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    spl4_12 <=> ! [X0] : (u1_struct_0(X0) = sK3(sK0,X0) | ~m1_pre_topc(X0,sK0) | v1_tex_2(X0,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    u1_struct_0(sK2) = sK3(sK0,sK2) | (~spl4_3 | spl4_5 | ~spl4_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f103,f50])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~m1_pre_topc(sK2,sK0) | u1_struct_0(sK2) = sK3(sK0,sK2) | (spl4_5 | ~spl4_12)),
% 0.20/0.53    inference(resolution,[],[f101,f60])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0] : (v1_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = sK3(sK0,X0)) ) | ~spl4_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f100])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl4_12 | ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f79,f38,f100])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0] : (u1_struct_0(X0) = sK3(sK0,X0) | ~m1_pre_topc(X0,sK0) | v1_tex_2(X0,sK0)) ) | ~spl4_1),
% 0.20/0.53    inference(resolution,[],[f32,f40])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    spl4_8 | ~spl4_2 | ~spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f72,f64,f43,f75])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    spl4_6 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    l1_pre_topc(sK1) | (~spl4_2 | ~spl4_6)),
% 0.20/0.53    inference(resolution,[],[f65,f45])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f64])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f68])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f5])).
% 0.20/0.53  fof(f5,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl4_6 | ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f62,f38,f64])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl4_1),
% 0.20/0.53    inference(resolution,[],[f29,f40])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.53  % (2759)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ~spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f27,f58])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ~v1_tex_2(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f53])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v1_tex_2(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f24,f48])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f22,f38])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (2761)------------------------------
% 0.20/0.53  % (2761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2761)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (2761)Memory used [KB]: 6268
% 0.20/0.53  % (2761)Time elapsed: 0.087 s
% 0.20/0.53  % (2761)------------------------------
% 0.20/0.53  % (2761)------------------------------
% 0.20/0.53  % (2758)Success in time 0.167 s
%------------------------------------------------------------------------------
