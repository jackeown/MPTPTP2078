%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 209 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 (1409 expanded)
%              Number of equality atoms :   17 ( 114 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f83,f105,f107,f110,f124,f127,f129,f131,f133])).

fof(f133,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl5_13 ),
    inference(resolution,[],[f117,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

fof(f117,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f131,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_9
    | ~ spl5_11
    | spl5_6 ),
    inference(avatar_split_clause,[],[f130,f81,f97,f91,f119,f116,f113])).

fof(f113,plain,
    ( spl5_12
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f119,plain,
    ( spl5_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f91,plain,
    ( spl5_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f97,plain,
    ( spl5_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f81,plain,
    ( spl5_6
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | spl5_6 ),
    inference(resolution,[],[f82,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f82,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f129,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl5_12 ),
    inference(resolution,[],[f114,f18])).

fof(f18,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f114,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f127,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_9
    | ~ spl5_11
    | spl5_5 ),
    inference(avatar_split_clause,[],[f125,f78,f97,f91,f119,f116,f113])).

fof(f78,plain,
    ( spl5_5
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | spl5_5 ),
    inference(resolution,[],[f79,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f124,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f120,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f120,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f110,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f98,f20])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f107,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f92,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f105,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f103,f72,f81,f78])).

fof(f72,plain,
    ( spl5_4
  <=> m1_subset_1(sK2(sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f103,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl5_4 ),
    inference(resolution,[],[f73,f14])).

fof(f14,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,
    ( ~ m1_subset_1(sK2(sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f83,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f75,f69,f81,f78])).

fof(f69,plain,
    ( spl5_3
  <=> v3_pre_topc(sK2(sK3(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl5_3 ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f20,f21,f22,f15,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v4_pre_topc(sK2(X0),sK0)
      | v3_pre_topc(sK2(X0),sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f26,f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f15,plain,(
    ! [X2] :
      ( v4_pre_topc(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,
    ( ~ v3_pre_topc(sK2(sK3(sK0,sK1)),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f74,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f72,f69])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2(sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2(sK3(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f19,f20,f22,f18,f17,f66])).

fof(f66,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2(sK3(sK0,sK1)),sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK3(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2(sK3(sK0,sK1)),sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(superposition,[],[f23,f64])).

fof(f64,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK3(sK0,sK1))) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1)) ),
    inference(global_subsumption,[],[f19,f20,f22,f18,f62])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK3(sK0,sK1))) = k6_domain_1(u1_struct_0(sK0),sK3(sK0,sK1)) ),
    inference(resolution,[],[f58,f17])).

fof(f58,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_tex_2(sK1,X1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK3(X1,sK1))) = k6_domain_1(u1_struct_0(sK0),sK3(X1,sK1)) ) ),
    inference(global_subsumption,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(sK1,X0)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(sK3(X0,sK1))) = k6_domain_1(u1_struct_0(sK0),sK3(X0,sK1)) ) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X0)) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(duplicate_literal_removal,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X0)) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f31,f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,X0)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X1)) = k6_domain_1(u1_struct_0(sK0),X1) ) ),
    inference(resolution,[],[f30,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK2(X2)) = k6_domain_1(u1_struct_0(sK0),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
