%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 334 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 (2391 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f79,f83,f129,f131,f133,f135,f137,f139,f141,f143,f162,f164,f166,f168,f170,f172,f174,f176,f178,f180])).

fof(f180,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_connsp_1(X3,X1)
                        & v3_tops_2(X2,X0,X1) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_connsp_1(X3,X1)
                      & v3_tops_2(X2,X0,X1) )
                   => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_2)).

fof(f92,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f178,plain,(
    ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl4_16 ),
    inference(resolution,[],[f128,f22])).

fof(f22,plain,(
    ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f128,plain,
    ( v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_16
  <=> v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f176,plain,(
    ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl4_13 ),
    inference(resolution,[],[f119,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f174,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_18 ),
    inference(resolution,[],[f151,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f151,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f172,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl4_19 ),
    inference(resolution,[],[f154,f24])).

fof(f24,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f154,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_19
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f170,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f161,f20])).

fof(f20,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f161,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_21
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f168,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | spl4_8 ),
    inference(avatar_split_clause,[],[f167,f103,f153,f150,f147])).

fof(f147,plain,
    ( spl4_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f103,plain,
    ( spl4_8
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f167,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl4_8 ),
    inference(resolution,[],[f104,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f104,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f166,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_17 ),
    inference(resolution,[],[f148,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f148,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f164,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | spl4_9 ),
    inference(avatar_split_clause,[],[f163,f106,f153,f150,f147])).

fof(f106,plain,
    ( spl4_9
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f163,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f107,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f162,plain,
    ( ~ spl4_21
    | ~ spl4_11
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_17
    | ~ spl4_14
    | spl4_6 ),
    inference(avatar_split_clause,[],[f145,f97,f121,f147,f153,f150,f112,f160])).

fof(f112,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f121,plain,
    ( spl4_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f97,plain,
    ( spl4_6
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | spl4_6 ),
    inference(resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(f98,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f143,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(global_subsumption,[],[f23,f24,f44])).

fof(f44,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f41,f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_10
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f101,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f139,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f95,f21])).

fof(f21,plain,(
    v2_connsp_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( ~ v2_connsp_1(sK3,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_5
  <=> v2_connsp_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f137,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f125,f27])).

fof(f27,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_15
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f135,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl4_14 ),
    inference(resolution,[],[f122,f28])).

fof(f28,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f133,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f116,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f116,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f131,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f113,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f129,plain,
    ( spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f89,f66,f127,f124,f121,f118,f115,f112,f109,f106,f103,f100,f97,f94,f91])).

fof(f66,plain,
    ( spl4_2
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,
    ( v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v2_connsp_1(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f40,f86])).

fof(f86,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f67,f19])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_connsp_1(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_connsp_1(X3,X0)
                      & v5_pre_topc(X2,X0,X1) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_2)).

fof(f83,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f75,f28])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_3 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f70,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f79,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f72,f31])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1 ),
    inference(resolution,[],[f64,f33])).

fof(f64,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f61,f69,f66,f63])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_struct_0(sK0)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    inference(global_subsumption,[],[f23,f24,f25,f49,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    inference(superposition,[],[f32,f58])).

fof(f58,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(global_subsumption,[],[f23,f28,f31,f20,f24,f56])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(global_subsumption,[],[f23,f28,f31,f20,f24,f47])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_funct_1(sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (21754)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.48  % (21770)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.49  % (21762)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.49  % (21756)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.49  % (21757)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.49  % (21754)Refutation not found, incomplete strategy% (21754)------------------------------
% 0.19/0.49  % (21754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (21754)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (21754)Memory used [KB]: 10618
% 0.19/0.49  % (21754)Time elapsed: 0.086 s
% 0.19/0.49  % (21754)------------------------------
% 0.19/0.49  % (21754)------------------------------
% 0.19/0.49  % (21774)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.50  % (21763)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (21764)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.50  % (21763)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f181,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f71,f79,f83,f129,f131,f133,f135,f137,f139,f141,f143,f162,f164,f166,f168,f170,f172,f174,f176,f178,f180])).
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    ~spl4_4),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f179])).
% 0.19/0.50  fof(f179,plain,(
% 0.19/0.50    $false | ~spl4_4),
% 0.19/0.50    inference(resolution,[],[f92,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f8])).
% 0.19/0.50  fof(f8,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & (v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1)) => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f6])).
% 0.19/0.50  fof(f6,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_connsp_1(X3,X1) & v3_tops_2(X2,X0,X1)) => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_2)).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    v2_struct_0(sK1) | ~spl4_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f91])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    spl4_4 <=> v2_struct_0(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.50  fof(f178,plain,(
% 0.19/0.50    ~spl4_16),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f177])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    $false | ~spl4_16),
% 0.19/0.50    inference(resolution,[],[f128,f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ~v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f128,plain,(
% 0.19/0.50    v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) | ~spl4_16),
% 0.19/0.50    inference(avatar_component_clause,[],[f127])).
% 0.19/0.50  fof(f127,plain,(
% 0.19/0.50    spl4_16 <=> v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    ~spl4_13),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f175])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    $false | ~spl4_13),
% 0.19/0.50    inference(resolution,[],[f119,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~spl4_13),
% 0.19/0.50    inference(avatar_component_clause,[],[f118])).
% 0.19/0.50  fof(f118,plain,(
% 0.19/0.50    spl4_13 <=> v2_struct_0(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    spl4_18),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f173])).
% 0.19/0.50  fof(f173,plain,(
% 0.19/0.50    $false | spl4_18),
% 0.19/0.50    inference(resolution,[],[f151,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f151,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl4_18),
% 0.19/0.50    inference(avatar_component_clause,[],[f150])).
% 0.19/0.50  fof(f150,plain,(
% 0.19/0.50    spl4_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    spl4_19),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    $false | spl4_19),
% 0.19/0.50    inference(resolution,[],[f154,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl4_19),
% 0.19/0.50    inference(avatar_component_clause,[],[f153])).
% 0.19/0.50  fof(f153,plain,(
% 0.19/0.50    spl4_19 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    spl4_21),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f169])).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    $false | spl4_21),
% 0.19/0.50    inference(resolution,[],[f161,f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    v3_tops_2(sK2,sK0,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f161,plain,(
% 0.19/0.50    ~v3_tops_2(sK2,sK0,sK1) | spl4_21),
% 0.19/0.50    inference(avatar_component_clause,[],[f160])).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    spl4_21 <=> v3_tops_2(sK2,sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ~spl4_17 | ~spl4_18 | ~spl4_19 | spl4_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f167,f103,f153,f150,f147])).
% 0.19/0.50  fof(f147,plain,(
% 0.19/0.50    spl4_17 <=> v1_funct_1(sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    spl4_8 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl4_8),
% 0.19/0.50    inference(resolution,[],[f104,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f103])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    spl4_17),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f165])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    $false | spl4_17),
% 0.19/0.50    inference(resolution,[],[f148,f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    v1_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f148,plain,(
% 0.19/0.50    ~v1_funct_1(sK2) | spl4_17),
% 0.19/0.50    inference(avatar_component_clause,[],[f147])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    ~spl4_17 | ~spl4_18 | ~spl4_19 | spl4_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f163,f106,f153,f150,f147])).
% 0.19/0.50  fof(f106,plain,(
% 0.19/0.50    spl4_9 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl4_9),
% 0.19/0.50    inference(resolution,[],[f107,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f106])).
% 0.19/0.50  fof(f162,plain,(
% 0.19/0.50    ~spl4_21 | ~spl4_11 | ~spl4_18 | ~spl4_19 | ~spl4_17 | ~spl4_14 | spl4_6),
% 0.19/0.50    inference(avatar_split_clause,[],[f145,f97,f121,f147,f153,f150,f112,f160])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    spl4_11 <=> l1_pre_topc(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.50  fof(f121,plain,(
% 0.19/0.50    spl4_14 <=> l1_pre_topc(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    spl4_6 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v3_tops_2(sK2,sK0,sK1) | spl4_6),
% 0.19/0.50    inference(resolution,[],[f98,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl4_6),
% 0.19/0.50    inference(avatar_component_clause,[],[f97])).
% 0.19/0.50  fof(f143,plain,(
% 0.19/0.50    spl4_10),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f142])).
% 0.19/0.50  fof(f142,plain,(
% 0.19/0.50    $false | spl4_10),
% 0.19/0.50    inference(resolution,[],[f110,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(global_subsumption,[],[f23,f24,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(resolution,[],[f41,f25])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl4_10),
% 0.19/0.50    inference(avatar_component_clause,[],[f109])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    spl4_10 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.50  fof(f141,plain,(
% 0.19/0.50    spl4_7),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    $false | spl4_7),
% 0.19/0.50    inference(resolution,[],[f101,f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f101,plain,(
% 0.19/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | spl4_7),
% 0.19/0.50    inference(avatar_component_clause,[],[f100])).
% 0.19/0.50  fof(f100,plain,(
% 0.19/0.50    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.50  fof(f139,plain,(
% 0.19/0.50    spl4_5),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f138])).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    $false | spl4_5),
% 0.19/0.50    inference(resolution,[],[f95,f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    v2_connsp_1(sK3,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    ~v2_connsp_1(sK3,sK1) | spl4_5),
% 0.19/0.50    inference(avatar_component_clause,[],[f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    spl4_5 <=> v2_connsp_1(sK3,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.50  fof(f137,plain,(
% 0.19/0.50    spl4_15),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f136])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    $false | spl4_15),
% 0.19/0.50    inference(resolution,[],[f125,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    v2_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f125,plain,(
% 0.19/0.50    ~v2_pre_topc(sK1) | spl4_15),
% 0.19/0.50    inference(avatar_component_clause,[],[f124])).
% 0.19/0.50  fof(f124,plain,(
% 0.19/0.50    spl4_15 <=> v2_pre_topc(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.50  fof(f135,plain,(
% 0.19/0.50    spl4_14),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f134])).
% 0.19/0.50  fof(f134,plain,(
% 0.19/0.50    $false | spl4_14),
% 0.19/0.50    inference(resolution,[],[f122,f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    l1_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | spl4_14),
% 0.19/0.50    inference(avatar_component_clause,[],[f121])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    spl4_12),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f132])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    $false | spl4_12),
% 0.19/0.50    inference(resolution,[],[f116,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    ~v2_pre_topc(sK0) | spl4_12),
% 0.19/0.50    inference(avatar_component_clause,[],[f115])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    spl4_12 <=> v2_pre_topc(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.50  fof(f131,plain,(
% 0.19/0.50    spl4_11),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f130])).
% 0.19/0.50  fof(f130,plain,(
% 0.19/0.50    $false | spl4_11),
% 0.19/0.50    inference(resolution,[],[f113,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0) | spl4_11),
% 0.19/0.50    inference(avatar_component_clause,[],[f112])).
% 0.19/0.50  fof(f129,plain,(
% 0.19/0.50    spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f89,f66,f127,f124,f121,f118,f115,f112,f109,f106,f103,f100,f97,f94,f91])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    spl4_2 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v2_connsp_1(sK3,sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.19/0.50    inference(superposition,[],[f40,f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | ~spl4_2),
% 0.19/0.50    inference(resolution,[],[f67,f19])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f66])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~v2_connsp_1(X3,X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v2_connsp_1(X3,X0) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | (~v2_connsp_1(X3,X0) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_connsp_1(X3,X0) & v5_pre_topc(X2,X0,X1)) => v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_2)).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    spl4_3),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    $false | spl4_3),
% 0.19/0.50    inference(resolution,[],[f75,f28])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | spl4_3),
% 0.19/0.50    inference(resolution,[],[f70,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    ~l1_struct_0(sK1) | spl4_3),
% 0.19/0.50    inference(avatar_component_clause,[],[f69])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    spl4_3 <=> l1_struct_0(sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    spl4_1),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f78])).
% 0.19/0.50  fof(f78,plain,(
% 0.19/0.50    $false | spl4_1),
% 0.19/0.50    inference(resolution,[],[f72,f31])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0) | spl4_1),
% 0.19/0.50    inference(resolution,[],[f64,f33])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f63])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    spl4_1 <=> l1_struct_0(sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ~spl4_1 | spl4_2 | ~spl4_3),
% 0.19/0.50    inference(avatar_split_clause,[],[f61,f69,f66,f63])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_struct_0(sK0) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) )),
% 0.19/0.50    inference(global_subsumption,[],[f23,f24,f25,f49,f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) )),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) )),
% 0.19/0.50    inference(superposition,[],[f32,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.19/0.50    inference(global_subsumption,[],[f23,f28,f31,f20,f24,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~v3_tops_2(sK2,sK0,sK1)),
% 0.19/0.50    inference(resolution,[],[f35,f25])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    v2_funct_1(sK2)),
% 0.19/0.50    inference(global_subsumption,[],[f23,f28,f31,f20,f24,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_funct_1(sK2) | ~v3_tops_2(sK2,sK0,sK1)),
% 0.19/0.50    inference(resolution,[],[f36,f25])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (21763)------------------------------
% 0.19/0.50  % (21763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (21763)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (21763)Memory used [KB]: 10746
% 0.19/0.50  % (21763)Time elapsed: 0.097 s
% 0.19/0.50  % (21763)------------------------------
% 0.19/0.50  % (21763)------------------------------
% 0.19/0.50  % (21746)Success in time 0.146 s
%------------------------------------------------------------------------------
