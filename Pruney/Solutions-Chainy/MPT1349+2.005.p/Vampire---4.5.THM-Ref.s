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
% DateTime   : Thu Dec  3 13:14:41 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  308 ( 884 expanded)
%              Number of leaves         :   60 ( 410 expanded)
%              Depth                    :   12
%              Number of atoms          : 1821 (5489 expanded)
%              Number of equality atoms :  184 ( 789 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f87,f91,f99,f103,f107,f120,f136,f140,f161,f166,f193,f195,f204,f211,f215,f219,f221,f223,f225,f238,f244,f272,f290,f301,f314,f316,f318,f321,f328,f344,f348,f396,f468,f472,f506,f515,f534,f582,f609,f653,f783,f786,f793,f823,f834,f1182,f1198,f1300,f1380,f1395,f1419,f1421])).

fof(f1421,plain,
    ( ~ spl6_8
    | ~ spl6_1
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34
    | spl6_23
    | spl6_35 ),
    inference(avatar_split_clause,[],[f1420,f294,f209,f288,f156,f153,f150,f78,f113])).

fof(f113,plain,
    ( spl6_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f78,plain,
    ( spl6_1
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f150,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f153,plain,
    ( spl6_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f156,plain,
    ( spl6_15
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f288,plain,
    ( spl6_34
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f209,plain,
    ( spl6_23
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f294,plain,
    ( spl6_35
  <=> v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1420,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl6_35 ),
    inference(resolution,[],[f368,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(f368,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1419,plain,
    ( ~ spl6_35
    | ~ spl6_34
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_8
    | spl6_36 ),
    inference(avatar_split_clause,[],[f1402,f297,f113,f266,f263,f260,f288,f294])).

fof(f260,plain,
    ( spl6_28
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f263,plain,
    ( spl6_29
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f266,plain,
    ( spl6_30
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f297,plain,
    ( spl6_36
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1402,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_36 ),
    inference(resolution,[],[f298,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f298,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | spl6_36 ),
    inference(avatar_component_clause,[],[f297])).

fof(f1395,plain,
    ( ~ spl6_15
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_35
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_8
    | spl6_33 ),
    inference(avatar_split_clause,[],[f1393,f284,f113,f288,f266,f294,f153,f150,f156])).

fof(f284,plain,
    ( spl6_33
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1393,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_33 ),
    inference(resolution,[],[f285,f398])).

fof(f398,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f127,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f285,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1380,plain,
    ( ~ spl6_30
    | ~ spl6_34
    | ~ spl6_38
    | spl6_23
    | ~ spl6_14
    | ~ spl6_13
    | ~ spl6_15
    | spl6_5
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_35
    | ~ spl6_41
    | ~ spl6_173 ),
    inference(avatar_split_clause,[],[f1378,f1298,f342,f294,f242,f101,f94,f156,f150,f153,f209,f312,f288,f266])).

fof(f312,plain,
    ( spl6_38
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f94,plain,
    ( spl6_5
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f101,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f242,plain,
    ( spl6_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f342,plain,
    ( spl6_41
  <=> ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1298,plain,
    ( spl6_173
  <=> ! [X9,X8] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
        | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).

fof(f1378,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_35
    | ~ spl6_41
    | ~ spl6_173 ),
    inference(forward_demodulation,[],[f1377,f1252])).

fof(f1252,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | ~ spl6_6
    | ~ spl6_41 ),
    inference(resolution,[],[f102,f343])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f342])).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1377,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_6
    | ~ spl6_26
    | ~ spl6_35
    | ~ spl6_173 ),
    inference(forward_demodulation,[],[f1374,f1250])).

fof(f1250,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl6_6
    | ~ spl6_26 ),
    inference(resolution,[],[f102,f243])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f242])).

fof(f1374,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_35
    | ~ spl6_173 ),
    inference(resolution,[],[f1299,f295])).

fof(f295,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1299,plain,
    ( ! [X8,X9] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
        | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
        | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9)) )
    | ~ spl6_173 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1300,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_173
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1278,f101,f1298,f113,f186])).

fof(f186,plain,
    ( spl6_19
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f1278,plain,
    ( ! [X8,X9] :
        ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3))
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8))))
        | ~ v1_funct_1(X9) )
    | ~ spl6_6 ),
    inference(resolution,[],[f102,f479])).

fof(f479,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0))
      | ~ v2_pre_topc(X1)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f170,f75])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f66,f76])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).

fof(f1198,plain,
    ( ~ spl6_36
    | ~ spl6_19
    | ~ spl6_110
    | ~ spl6_102
    | ~ spl6_103
    | ~ spl6_77
    | ~ spl6_34
    | ~ spl6_38
    | spl6_23
    | ~ spl6_8
    | spl6_67
    | ~ spl6_109
    | ~ spl6_157 ),
    inference(avatar_split_clause,[],[f1196,f1180,f821,f513,f113,f209,f312,f288,f578,f775,f772,f826,f186,f297])).

fof(f826,plain,
    ( spl6_110
  <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f772,plain,
    ( spl6_102
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f775,plain,
    ( spl6_103
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f578,plain,
    ( spl6_77
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f513,plain,
    ( spl6_67
  <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f821,plain,
    ( spl6_109
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f1180,plain,
    ( spl6_157
  <=> k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).

fof(f1196,plain,
    ( r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ spl6_109
    | ~ spl6_157 ),
    inference(forward_demodulation,[],[f1194,f822])).

fof(f822,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2))
    | ~ spl6_109 ),
    inference(avatar_component_clause,[],[f821])).

fof(f1194,plain,
    ( r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)
    | ~ spl6_157 ),
    inference(superposition,[],[f70,f1181])).

fof(f1181,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl6_157 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

fof(f1182,plain,
    ( spl6_23
    | ~ spl6_38
    | ~ spl6_34
    | ~ spl6_15
    | ~ spl6_14
    | spl6_10
    | spl6_157
    | ~ spl6_81
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f1178,f791,f607,f1180,f130,f153,f156,f288,f312,f209])).

fof(f130,plain,
    ( spl6_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f607,plain,
    ( spl6_81
  <=> ! [X1,X2] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f791,plain,
    ( spl6_105
  <=> k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f1178,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_81
    | ~ spl6_105 ),
    inference(forward_demodulation,[],[f1177,f792])).

fof(f792,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f791])).

fof(f1177,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_81 ),
    inference(resolution,[],[f608,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).

fof(f608,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X2,sK0,X1)
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f607])).

fof(f834,plain,
    ( spl6_10
    | ~ spl6_19
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34
    | ~ spl6_38
    | spl6_23
    | ~ spl6_8
    | spl6_110 ),
    inference(avatar_split_clause,[],[f833,f826,f113,f209,f312,f288,f156,f153,f150,f186,f130])).

fof(f833,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl6_110 ),
    inference(resolution,[],[f827,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f827,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_110 ),
    inference(avatar_component_clause,[],[f826])).

fof(f823,plain,
    ( spl6_23
    | ~ spl6_38
    | ~ spl6_34
    | ~ spl6_15
    | ~ spl6_14
    | spl6_10
    | spl6_109
    | ~ spl6_60
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f819,f532,f470,f821,f130,f153,f156,f288,f312,f209])).

fof(f470,plain,
    ( spl6_60
  <=> ! [X1,X2] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f532,plain,
    ( spl6_70
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f819,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_60
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f818,f533])).

fof(f533,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f532])).

fof(f818,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_60 ),
    inference(resolution,[],[f471,f45])).

fof(f471,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X2,sK0,X1)
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f470])).

fof(f793,plain,
    ( spl6_23
    | ~ spl6_38
    | ~ spl6_34
    | ~ spl6_15
    | ~ spl6_14
    | spl6_10
    | spl6_105
    | ~ spl6_49
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f789,f504,f394,f791,f130,f153,f156,f288,f312,f209])).

fof(f394,plain,
    ( spl6_49
  <=> ! [X1,X2] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f504,plain,
    ( spl6_66
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f789,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_49
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f788,f505])).

fof(f505,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f504])).

fof(f788,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_49 ),
    inference(resolution,[],[f395,f45])).

fof(f395,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X2,sK0,X1)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f394])).

fof(f786,plain,
    ( ~ spl6_30
    | ~ spl6_28
    | ~ spl6_29
    | spl6_102 ),
    inference(avatar_split_clause,[],[f785,f772,f263,f260,f266])).

fof(f785,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl6_102 ),
    inference(resolution,[],[f773,f76])).

fof(f773,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_102 ),
    inference(avatar_component_clause,[],[f772])).

fof(f783,plain,
    ( ~ spl6_30
    | ~ spl6_28
    | ~ spl6_29
    | spl6_103 ),
    inference(avatar_split_clause,[],[f782,f775,f263,f260,f266])).

fof(f782,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl6_103 ),
    inference(resolution,[],[f776,f75])).

fof(f776,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_103 ),
    inference(avatar_component_clause,[],[f775])).

fof(f653,plain,
    ( spl6_35
    | spl6_23
    | ~ spl6_11
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_8
    | ~ spl6_19
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f652,f342,f309,f242,f213,f206,f105,f312,f288,f186,f113,f266,f263,f260,f144,f209,f294])).

fof(f144,plain,
    ( spl6_11
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f105,plain,
    ( spl6_7
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f206,plain,
    ( spl6_22
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f213,plain,
    ( spl6_24
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f309,plain,
    ( spl6_37
  <=> m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f652,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f650,f214])).

fof(f214,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f650,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(trivial_inequality_removal,[],[f649])).

fof(f649,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f648,f207])).

fof(f207,plain,
    ( k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f648,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(trivial_inequality_removal,[],[f647])).

fof(f647,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f646,f349])).

fof(f349,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(resolution,[],[f310,f243])).

fof(f310,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f309])).

fof(f646,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_7
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(superposition,[],[f65,f634])).

fof(f634,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_7
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f387,f350])).

fof(f350,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_7
    | ~ spl6_37 ),
    inference(resolution,[],[f310,f106])).

fof(f106,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f387,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(resolution,[],[f343,f310])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f609,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_81
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f601,f466,f607,f113,f186])).

fof(f466,plain,
    ( spl6_59
  <=> ! [X0] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f601,plain,
    ( ! [X2,X1] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_59 ),
    inference(resolution,[],[f467,f71])).

fof(f467,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0)) )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f466])).

fof(f582,plain,
    ( ~ spl6_14
    | ~ spl6_30
    | ~ spl6_29
    | ~ spl6_15
    | ~ spl6_13
    | spl6_77 ),
    inference(avatar_split_clause,[],[f581,f578,f150,f156,f263,f266,f153])).

fof(f581,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_77 ),
    inference(resolution,[],[f579,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
      | ~ v1_funct_1(k2_tops_2(X1,X2,X0))
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f76,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f579,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | spl6_77 ),
    inference(avatar_component_clause,[],[f578])).

fof(f534,plain,
    ( spl6_23
    | ~ spl6_38
    | ~ spl6_34
    | ~ spl6_15
    | ~ spl6_14
    | spl6_70
    | spl6_10
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f530,f346,f130,f532,f153,f156,f288,f312,f209])).

fof(f346,plain,
    ( spl6_42
  <=> ! [X1,X2] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f530,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f347,f45])).

fof(f347,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X2,sK0,X1)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f346])).

fof(f515,plain,
    ( spl6_10
    | ~ spl6_19
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34
    | ~ spl6_38
    | spl6_23
    | ~ spl6_8
    | ~ spl6_67
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f509,f504,f513,f113,f209,f312,f288,f156,f153,f150,f186,f130])).

fof(f509,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_66 ),
    inference(superposition,[],[f72,f505])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f506,plain,
    ( spl6_23
    | ~ spl6_38
    | ~ spl6_34
    | ~ spl6_15
    | ~ spl6_14
    | spl6_66
    | spl6_10
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f373,f200,f130,f504,f153,f156,f288,f312,f209])).

fof(f200,plain,
    ( spl6_21
  <=> ! [X1,X2] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f373,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_21 ),
    inference(resolution,[],[f201,f45])).

fof(f201,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v5_pre_topc(X2,sK0,X1)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f472,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_60
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f464,f270,f470,f113,f186])).

fof(f270,plain,
    ( spl6_31
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f464,plain,
    ( ! [X2,X1] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_31 ),
    inference(resolution,[],[f271,f71])).

fof(f271,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f468,plain,
    ( ~ spl6_8
    | spl6_59
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f462,f270,f466,f113])).

fof(f462,plain,
    ( ! [X0] :
        ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_31 ),
    inference(resolution,[],[f271,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f396,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_49
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f388,f342,f394,f113,f186])).

fof(f388,plain,
    ( ! [X2,X1] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_41 ),
    inference(resolution,[],[f343,f71])).

fof(f348,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_42
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f340,f242,f346,f113,f186])).

fof(f340,plain,
    ( ! [X2,X1] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_26 ),
    inference(resolution,[],[f243,f71])).

fof(f344,plain,
    ( ~ spl6_8
    | spl6_41
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f339,f242,f342,f113])).

fof(f339,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_26 ),
    inference(resolution,[],[f243,f73])).

fof(f328,plain,
    ( ~ spl6_15
    | ~ spl6_13
    | ~ spl6_14
    | spl6_28 ),
    inference(avatar_split_clause,[],[f327,f260,f153,f150,f156])).

fof(f327,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_28 ),
    inference(resolution,[],[f261,f76])).

fof(f261,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f260])).

fof(f321,plain,
    ( ~ spl6_15
    | ~ spl6_13
    | ~ spl6_14
    | spl6_29 ),
    inference(avatar_split_clause,[],[f320,f263,f153,f150,f156])).

fof(f320,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_29 ),
    inference(resolution,[],[f264,f75])).

fof(f264,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f263])).

fof(f318,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl6_30 ),
    inference(resolution,[],[f267,f122])).

fof(f122,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(global_subsumption,[],[f43,f44,f121])).

fof(f121,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f74,f45])).

fof(f44,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f267,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f316,plain,(
    spl6_38 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl6_38 ),
    inference(resolution,[],[f313,f47])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f313,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( spl6_35
    | spl6_37
    | ~ spl6_11
    | spl6_23
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_8
    | ~ spl6_19
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f307,f213,f206,f312,f288,f186,f113,f266,f263,f260,f209,f144,f309,f294])).

fof(f307,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(trivial_inequality_removal,[],[f306])).

fof(f306,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f304,f207])).

fof(f304,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_24 ),
    inference(trivial_inequality_removal,[],[f303])).

fof(f303,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_24 ),
    inference(superposition,[],[f64,f214])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f301,plain,(
    spl6_34 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl6_34 ),
    inference(resolution,[],[f289,f48])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl6_1
    | ~ spl6_33
    | ~ spl6_10
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_34
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f282,f89,f85,f288,f156,f153,f150,f113,f81,f130,f284,f78])).

fof(f81,plain,
    ( spl6_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f85,plain,
    ( spl6_3
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,
    ( spl6_4
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f280,f90])).

fof(f90,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f280,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f277])).

fof(f277,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(superposition,[],[f62,f86])).

fof(f86,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_funct_1(X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f272,plain,
    ( ~ spl6_11
    | ~ spl6_16
    | spl6_31
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_12
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f253,f213,f147,f266,f263,f260,f270,f159,f144])).

fof(f159,plain,
    ( spl6_16
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f147,plain,
    ( spl6_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f253,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK0)
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK1)
        | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1) )
    | ~ spl6_24 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( ! [X1] :
        ( k2_struct_0(sK0) != k2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK1)
        | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1) )
    | ~ spl6_24 ),
    inference(superposition,[],[f52,f214])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f244,plain,
    ( ~ spl6_2
    | ~ spl6_12
    | spl6_26
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f240,f85,f159,f156,f153,f150,f242,f147,f81])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( ! [X0] :
        ( k2_struct_0(sK1) != k2_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_3 ),
    inference(superposition,[],[f53,f86])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f238,plain,
    ( ~ spl6_19
    | ~ spl6_8
    | spl6_21
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f236,f105,f200,f113,f186])).

fof(f236,plain,
    ( ! [X2,X1] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_7 ),
    inference(resolution,[],[f106,f71])).

fof(f225,plain,(
    ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_23 ),
    inference(resolution,[],[f210,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f210,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f209])).

fof(f223,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f222,f81,f78])).

fof(f222,plain,
    ( v2_funct_1(sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f43,f48,f50,f44,f124])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_funct_1(sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f59,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f221,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f151,f45])).

fof(f151,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f219,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f154,f44])).

fof(f154,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f215,plain,
    ( spl6_24
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_23
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f168,f85,f209,f159,f156,f153,f150,f147,f81,f213])).

fof(f168,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(superposition,[],[f55,f86])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f211,plain,
    ( spl6_22
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_23
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f164,f85,f209,f159,f156,f153,f150,f147,f81,f206])).

fof(f164,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(superposition,[],[f54,f86])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f204,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f169,f48])).

fof(f169,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_16 ),
    inference(resolution,[],[f160,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f160,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f159])).

fof(f195,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f162,f50])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_12 ),
    inference(resolution,[],[f148,f56])).

fof(f148,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f193,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl6_19 ),
    inference(resolution,[],[f187,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f166,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_15 ),
    inference(resolution,[],[f157,f43])).

fof(f157,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f161,plain,
    ( spl6_11
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f142,f85,f159,f156,f153,f150,f147,f81,f144])).

fof(f142,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_3 ),
    inference(superposition,[],[f51,f86])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f140,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f139,f85,f78])).

fof(f139,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f43,f48,f50,f44,f137])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f136,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f135,f89,f78])).

fof(f135,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f43,f48,f50,f44,f133])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f120,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f114,f50])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f107,plain,
    ( spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f37,f105,f78])).

fof(f37,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( ~ spl6_1
    | spl6_6
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f38,f89,f85,f81,f101,f78])).

fof(f38,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f39,f89,f85,f81,f94,f78])).

fof(f39,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f40,f89,f78])).

fof(f40,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f41,f85,f78])).

fof(f41,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f42,f81,f78])).

fof(f42,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21974)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.48  % (21966)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.48  % (21966)Refutation not found, incomplete strategy% (21966)------------------------------
% 0.21/0.48  % (21966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21966)Memory used [KB]: 10746
% 0.21/0.48  % (21966)Time elapsed: 0.069 s
% 0.21/0.48  % (21966)------------------------------
% 0.21/0.48  % (21966)------------------------------
% 0.21/0.49  % (21963)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (21972)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (21960)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (21962)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (21971)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (21961)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (21980)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (21970)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (21965)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (21961)Refutation not found, incomplete strategy% (21961)------------------------------
% 0.21/0.51  % (21961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21961)Memory used [KB]: 10618
% 0.21/0.51  % (21961)Time elapsed: 0.093 s
% 0.21/0.51  % (21961)------------------------------
% 0.21/0.51  % (21961)------------------------------
% 0.21/0.51  % (21959)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (21958)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (21978)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (21981)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (21969)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (21975)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (21964)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (21976)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (21977)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (21979)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (21967)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (21968)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.53  % (21973)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.86/0.62  % (21970)Refutation found. Thanks to Tanya!
% 1.86/0.62  % SZS status Theorem for theBenchmark
% 1.86/0.62  % SZS output start Proof for theBenchmark
% 1.86/0.62  fof(f1422,plain,(
% 1.86/0.62    $false),
% 1.86/0.62    inference(avatar_sat_refutation,[],[f83,f87,f91,f99,f103,f107,f120,f136,f140,f161,f166,f193,f195,f204,f211,f215,f219,f221,f223,f225,f238,f244,f272,f290,f301,f314,f316,f318,f321,f328,f344,f348,f396,f468,f472,f506,f515,f534,f582,f609,f653,f783,f786,f793,f823,f834,f1182,f1198,f1300,f1380,f1395,f1419,f1421])).
% 1.86/0.62  fof(f1421,plain,(
% 1.86/0.62    ~spl6_8 | ~spl6_1 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_34 | spl6_23 | spl6_35),
% 1.86/0.62    inference(avatar_split_clause,[],[f1420,f294,f209,f288,f156,f153,f150,f78,f113])).
% 1.86/0.62  fof(f113,plain,(
% 1.86/0.62    spl6_8 <=> l1_pre_topc(sK0)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.86/0.62  fof(f78,plain,(
% 1.86/0.62    spl6_1 <=> v3_tops_2(sK2,sK0,sK1)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.86/0.62  fof(f150,plain,(
% 1.86/0.62    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.86/0.62  fof(f153,plain,(
% 1.86/0.62    spl6_14 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.86/0.62  fof(f156,plain,(
% 1.86/0.62    spl6_15 <=> v1_funct_1(sK2)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.86/0.62  fof(f288,plain,(
% 1.86/0.62    spl6_34 <=> l1_pre_topc(sK1)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.86/0.62  fof(f209,plain,(
% 1.86/0.62    spl6_23 <=> v2_struct_0(sK1)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.86/0.62  fof(f294,plain,(
% 1.86/0.62    spl6_35 <=> v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.86/0.62  fof(f1420,plain,(
% 1.86/0.62    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | spl6_35),
% 1.86/0.62    inference(resolution,[],[f368,f63])).
% 1.86/0.62  fof(f63,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X0)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f28])).
% 1.86/0.62  fof(f28,plain,(
% 1.86/0.62    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 1.86/0.62    inference(flattening,[],[f27])).
% 1.86/0.62  fof(f27,plain,(
% 1.86/0.62    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 1.86/0.62    inference(ennf_transformation,[],[f10])).
% 1.86/0.62  fof(f10,axiom,(
% 1.86/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 1.86/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).
% 1.86/0.62  fof(f368,plain,(
% 1.86/0.62    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_35),
% 1.86/0.62    inference(avatar_component_clause,[],[f294])).
% 1.86/0.62  fof(f1419,plain,(
% 1.86/0.62    ~spl6_35 | ~spl6_34 | ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_8 | spl6_36),
% 1.86/0.62    inference(avatar_split_clause,[],[f1402,f297,f113,f266,f263,f260,f288,f294])).
% 1.86/0.62  fof(f260,plain,(
% 1.86/0.62    spl6_28 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.86/0.62  fof(f263,plain,(
% 1.86/0.62    spl6_29 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.86/0.62  fof(f266,plain,(
% 1.86/0.62    spl6_30 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.86/0.62  fof(f297,plain,(
% 1.86/0.62    spl6_36 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1)),
% 1.86/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.86/0.62  fof(f1402,plain,(
% 1.86/0.62    ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_36),
% 1.86/0.62    inference(resolution,[],[f298,f61])).
% 1.86/0.62  fof(f61,plain,(
% 1.86/0.62    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 1.86/0.62    inference(cnf_transformation,[],[f26])).
% 1.86/0.62  fof(f26,plain,(
% 1.86/0.62    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.86/0.62    inference(flattening,[],[f25])).
% 1.86/0.62  fof(f25,plain,(
% 1.86/0.62    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.86/0.62    inference(ennf_transformation,[],[f3])).
% 2.12/0.64  fof(f3,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 2.12/0.64  fof(f298,plain,(
% 2.12/0.64    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) | spl6_36),
% 2.12/0.64    inference(avatar_component_clause,[],[f297])).
% 2.12/0.64  fof(f1395,plain,(
% 2.12/0.64    ~spl6_15 | ~spl6_13 | ~spl6_14 | ~spl6_35 | ~spl6_30 | ~spl6_34 | ~spl6_8 | spl6_33),
% 2.12/0.64    inference(avatar_split_clause,[],[f1393,f284,f113,f288,f266,f294,f153,f150,f156])).
% 2.12/0.64  fof(f284,plain,(
% 2.12/0.64    spl6_33 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.12/0.64  fof(f1393,plain,(
% 2.12/0.64    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_33),
% 2.12/0.64    inference(resolution,[],[f285,f398])).
% 2.12/0.64  fof(f398,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2)) )),
% 2.12/0.64    inference(duplicate_literal_removal,[],[f397])).
% 2.12/0.64  fof(f397,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2)) )),
% 2.12/0.64    inference(resolution,[],[f127,f75])).
% 2.12/0.64  fof(f75,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f36])).
% 2.12/0.64  fof(f36,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.12/0.64    inference(flattening,[],[f35])).
% 2.12/0.64  fof(f35,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.12/0.64    inference(ennf_transformation,[],[f4])).
% 2.12/0.64  fof(f4,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 2.12/0.64  fof(f127,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X2)) )),
% 2.12/0.64    inference(resolution,[],[f60,f76])).
% 2.12/0.64  fof(f76,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f36])).
% 2.12/0.64  fof(f60,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f26])).
% 2.12/0.64  fof(f285,plain,(
% 2.12/0.64    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_33),
% 2.12/0.64    inference(avatar_component_clause,[],[f284])).
% 2.12/0.64  fof(f1380,plain,(
% 2.12/0.64    ~spl6_30 | ~spl6_34 | ~spl6_38 | spl6_23 | ~spl6_14 | ~spl6_13 | ~spl6_15 | spl6_5 | ~spl6_6 | ~spl6_26 | ~spl6_35 | ~spl6_41 | ~spl6_173),
% 2.12/0.64    inference(avatar_split_clause,[],[f1378,f1298,f342,f294,f242,f101,f94,f156,f150,f153,f209,f312,f288,f266])).
% 2.12/0.64  fof(f312,plain,(
% 2.12/0.64    spl6_38 <=> v2_pre_topc(sK1)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.12/0.64  fof(f94,plain,(
% 2.12/0.64    spl6_5 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.12/0.64  fof(f101,plain,(
% 2.12/0.64    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.12/0.64  fof(f242,plain,(
% 2.12/0.64    spl6_26 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.12/0.64  fof(f342,plain,(
% 2.12/0.64    spl6_41 <=> ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.12/0.64  fof(f1298,plain,(
% 2.12/0.64    spl6_173 <=> ! [X9,X8] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0) | ~v1_funct_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3)) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_173])])).
% 2.12/0.64  fof(f1378,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl6_6 | ~spl6_26 | ~spl6_35 | ~spl6_41 | ~spl6_173)),
% 2.12/0.64    inference(forward_demodulation,[],[f1377,f1252])).
% 2.12/0.64  fof(f1252,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) | (~spl6_6 | ~spl6_41)),
% 2.12/0.64    inference(resolution,[],[f102,f343])).
% 2.12/0.64  fof(f343,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))) ) | ~spl6_41),
% 2.12/0.64    inference(avatar_component_clause,[],[f342])).
% 2.12/0.64  fof(f102,plain,(
% 2.12/0.64    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 2.12/0.64    inference(avatar_component_clause,[],[f101])).
% 2.12/0.64  fof(f1377,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl6_6 | ~spl6_26 | ~spl6_35 | ~spl6_173)),
% 2.12/0.64    inference(forward_demodulation,[],[f1374,f1250])).
% 2.12/0.64  fof(f1250,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | (~spl6_6 | ~spl6_26)),
% 2.12/0.64    inference(resolution,[],[f102,f243])).
% 2.12/0.64  fof(f243,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_26),
% 2.12/0.64    inference(avatar_component_clause,[],[f242])).
% 2.12/0.64  fof(f1374,plain,(
% 2.12/0.64    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl6_35 | ~spl6_173)),
% 2.12/0.64    inference(resolution,[],[f1299,f295])).
% 2.12/0.64  fof(f295,plain,(
% 2.12/0.64    v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_35),
% 2.12/0.64    inference(avatar_component_clause,[],[f294])).
% 2.12/0.64  fof(f1299,plain,(
% 2.12/0.64    ( ! [X8,X9] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0) | ~v1_funct_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3)) | v2_struct_0(X8) | ~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9))) ) | ~spl6_173),
% 2.12/0.64    inference(avatar_component_clause,[],[f1298])).
% 2.12/0.64  fof(f1300,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_173 | ~spl6_6),
% 2.12/0.64    inference(avatar_split_clause,[],[f1278,f101,f1298,f113,f186])).
% 2.12/0.64  fof(f186,plain,(
% 2.12/0.64    spl6_19 <=> v2_pre_topc(sK0)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.12/0.64  fof(f1278,plain,(
% 2.12/0.64    ( ! [X8,X9] : (~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),X8,sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),k2_pre_topc(sK0,sK3)) = k2_pre_topc(X8,k8_relset_1(u1_struct_0(X8),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X8),X9),sK3)) | ~v2_pre_topc(sK0) | ~v1_funct_2(X9,u1_struct_0(sK0),u1_struct_0(X8)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X8)))) | ~v1_funct_1(X9)) ) | ~spl6_6),
% 2.12/0.64    inference(resolution,[],[f102,f479])).
% 2.12/0.64  fof(f479,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (~v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)) | ~v2_pre_topc(X1) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X3)) )),
% 2.12/0.64    inference(duplicate_literal_removal,[],[f473])).
% 2.12/0.64  fof(f473,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)) | ~v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X3)) )),
% 2.12/0.64    inference(resolution,[],[f170,f75])).
% 2.12/0.64  fof(f170,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),k2_pre_topc(X1,X0)) = k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X0)) | ~v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_1(X3)) )),
% 2.12/0.64    inference(resolution,[],[f66,f76])).
% 2.12/0.64  fof(f66,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f30])).
% 2.12/0.64  fof(f30,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.12/0.64    inference(flattening,[],[f29])).
% 2.12/0.64  fof(f29,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f11])).
% 2.12/0.64  fof(f11,axiom,(
% 2.12/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).
% 2.12/0.64  fof(f1198,plain,(
% 2.12/0.64    ~spl6_36 | ~spl6_19 | ~spl6_110 | ~spl6_102 | ~spl6_103 | ~spl6_77 | ~spl6_34 | ~spl6_38 | spl6_23 | ~spl6_8 | spl6_67 | ~spl6_109 | ~spl6_157),
% 2.12/0.64    inference(avatar_split_clause,[],[f1196,f1180,f821,f513,f113,f209,f312,f288,f578,f775,f772,f826,f186,f297])).
% 2.12/0.64  fof(f826,plain,(
% 2.12/0.64    spl6_110 <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 2.12/0.64  fof(f772,plain,(
% 2.12/0.64    spl6_102 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 2.12/0.64  fof(f775,plain,(
% 2.12/0.64    spl6_103 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 2.12/0.64  fof(f578,plain,(
% 2.12/0.64    spl6_77 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 2.12/0.64  fof(f513,plain,(
% 2.12/0.64    spl6_67 <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 2.12/0.64  fof(f821,plain,(
% 2.12/0.64    spl6_109 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).
% 2.12/0.64  fof(f1180,plain,(
% 2.12/0.64    spl6_157 <=> k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).
% 2.12/0.64  fof(f1196,plain,(
% 2.12/0.64    r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) | (~spl6_109 | ~spl6_157)),
% 2.12/0.64    inference(forward_demodulation,[],[f1194,f822])).
% 2.12/0.64  fof(f822,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2)) | ~spl6_109),
% 2.12/0.64    inference(avatar_component_clause,[],[f821])).
% 2.12/0.64  fof(f1194,plain,(
% 2.12/0.64    r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK0,sK1) | ~spl6_157),
% 2.12/0.64    inference(superposition,[],[f70,f1181])).
% 2.12/0.64  fof(f1181,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | ~spl6_157),
% 2.12/0.64    inference(avatar_component_clause,[],[f1180])).
% 2.12/0.64  fof(f70,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f32])).
% 2.12/0.64  fof(f32,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f31])).
% 2.12/0.64  fof(f31,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f5])).
% 2.12/0.64  fof(f5,axiom,(
% 2.12/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).
% 2.12/0.64  fof(f1182,plain,(
% 2.12/0.64    spl6_23 | ~spl6_38 | ~spl6_34 | ~spl6_15 | ~spl6_14 | spl6_10 | spl6_157 | ~spl6_81 | ~spl6_105),
% 2.12/0.64    inference(avatar_split_clause,[],[f1178,f791,f607,f1180,f130,f153,f156,f288,f312,f209])).
% 2.12/0.64  fof(f130,plain,(
% 2.12/0.64    spl6_10 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.12/0.64  fof(f607,plain,(
% 2.12/0.64    spl6_81 <=> ! [X1,X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 2.12/0.64  fof(f791,plain,(
% 2.12/0.64    spl6_105 <=> k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 2.12/0.64  fof(f1178,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_81 | ~spl6_105)),
% 2.12/0.64    inference(forward_demodulation,[],[f1177,f792])).
% 2.12/0.64  fof(f792,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | ~spl6_105),
% 2.12/0.64    inference(avatar_component_clause,[],[f791])).
% 2.12/0.64  fof(f1177,plain,(
% 2.12/0.64    v5_pre_topc(sK2,sK0,sK1) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_81),
% 2.12/0.64    inference(resolution,[],[f608,f45])).
% 2.12/0.64  fof(f45,plain,(
% 2.12/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f15,plain,(
% 2.12/0.64    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f14])).
% 2.12/0.64  fof(f14,plain,(
% 2.12/0.64    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f13])).
% 2.12/0.64  fof(f13,negated_conjecture,(
% 2.12/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 2.12/0.64    inference(negated_conjecture,[],[f12])).
% 2.12/0.64  fof(f12,conjecture,(
% 2.12/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).
% 2.12/0.64  fof(f608,plain,(
% 2.12/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_81),
% 2.12/0.64    inference(avatar_component_clause,[],[f607])).
% 2.12/0.64  fof(f834,plain,(
% 2.12/0.64    spl6_10 | ~spl6_19 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_34 | ~spl6_38 | spl6_23 | ~spl6_8 | spl6_110),
% 2.12/0.64    inference(avatar_split_clause,[],[f833,f826,f113,f209,f312,f288,f156,f153,f150,f186,f130])).
% 2.12/0.64  fof(f833,plain,(
% 2.12/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(sK2,sK0,sK1) | spl6_110),
% 2.12/0.64    inference(resolution,[],[f827,f71])).
% 2.12/0.64  fof(f71,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f32])).
% 2.12/0.64  fof(f827,plain,(
% 2.12/0.64    ~m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_110),
% 2.12/0.64    inference(avatar_component_clause,[],[f826])).
% 2.12/0.64  fof(f823,plain,(
% 2.12/0.64    spl6_23 | ~spl6_38 | ~spl6_34 | ~spl6_15 | ~spl6_14 | spl6_10 | spl6_109 | ~spl6_60 | ~spl6_70),
% 2.12/0.64    inference(avatar_split_clause,[],[f819,f532,f470,f821,f130,f153,f156,f288,f312,f209])).
% 2.12/0.64  fof(f470,plain,(
% 2.12/0.64    spl6_60 <=> ! [X1,X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2)) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 2.12/0.64  fof(f532,plain,(
% 2.12/0.64    spl6_70 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 2.12/0.64  fof(f819,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2)) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_60 | ~spl6_70)),
% 2.12/0.64    inference(forward_demodulation,[],[f818,f533])).
% 2.12/0.64  fof(f533,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2)) | ~spl6_70),
% 2.12/0.64    inference(avatar_component_clause,[],[f532])).
% 2.12/0.64  fof(f818,plain,(
% 2.12/0.64    v5_pre_topc(sK2,sK0,sK1) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,sK1,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_60),
% 2.12/0.64    inference(resolution,[],[f471,f45])).
% 2.12/0.64  fof(f471,plain,(
% 2.12/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_60),
% 2.12/0.64    inference(avatar_component_clause,[],[f470])).
% 2.12/0.64  fof(f793,plain,(
% 2.12/0.64    spl6_23 | ~spl6_38 | ~spl6_34 | ~spl6_15 | ~spl6_14 | spl6_10 | spl6_105 | ~spl6_49 | ~spl6_66),
% 2.12/0.64    inference(avatar_split_clause,[],[f789,f504,f394,f791,f130,f153,f156,f288,f312,f209])).
% 2.12/0.64  fof(f394,plain,(
% 2.12/0.64    spl6_49 <=> ! [X1,X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 2.12/0.64  fof(f504,plain,(
% 2.12/0.64    spl6_66 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 2.12/0.64  fof(f789,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_49 | ~spl6_66)),
% 2.12/0.64    inference(forward_demodulation,[],[f788,f505])).
% 2.12/0.64  fof(f505,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) | ~spl6_66),
% 2.12/0.64    inference(avatar_component_clause,[],[f504])).
% 2.12/0.64  fof(f788,plain,(
% 2.12/0.64    v5_pre_topc(sK2,sK0,sK1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_49),
% 2.12/0.64    inference(resolution,[],[f395,f45])).
% 2.12/0.64  fof(f395,plain,(
% 2.12/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_49),
% 2.12/0.64    inference(avatar_component_clause,[],[f394])).
% 2.12/0.64  fof(f786,plain,(
% 2.12/0.64    ~spl6_30 | ~spl6_28 | ~spl6_29 | spl6_102),
% 2.12/0.64    inference(avatar_split_clause,[],[f785,f772,f263,f260,f266])).
% 2.12/0.64  fof(f785,plain,(
% 2.12/0.64    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl6_102),
% 2.12/0.64    inference(resolution,[],[f773,f76])).
% 2.12/0.64  fof(f773,plain,(
% 2.12/0.64    ~m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_102),
% 2.12/0.64    inference(avatar_component_clause,[],[f772])).
% 2.12/0.64  fof(f783,plain,(
% 2.12/0.64    ~spl6_30 | ~spl6_28 | ~spl6_29 | spl6_103),
% 2.12/0.64    inference(avatar_split_clause,[],[f782,f775,f263,f260,f266])).
% 2.12/0.64  fof(f782,plain,(
% 2.12/0.64    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl6_103),
% 2.12/0.64    inference(resolution,[],[f776,f75])).
% 2.12/0.64  fof(f776,plain,(
% 2.12/0.64    ~v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_103),
% 2.12/0.64    inference(avatar_component_clause,[],[f775])).
% 2.12/0.64  fof(f653,plain,(
% 2.12/0.64    spl6_35 | spl6_23 | ~spl6_11 | ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_8 | ~spl6_19 | ~spl6_34 | ~spl6_38 | ~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_26 | ~spl6_37 | ~spl6_41),
% 2.12/0.64    inference(avatar_split_clause,[],[f652,f342,f309,f242,f213,f206,f105,f312,f288,f186,f113,f266,f263,f260,f144,f209,f294])).
% 2.12/0.64  fof(f144,plain,(
% 2.12/0.64    spl6_11 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.12/0.64  fof(f105,plain,(
% 2.12/0.64    spl6_7 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.12/0.64  fof(f206,plain,(
% 2.12/0.64    spl6_22 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.12/0.64  fof(f213,plain,(
% 2.12/0.64    spl6_24 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.12/0.64  fof(f309,plain,(
% 2.12/0.64    spl6_37 <=> m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.12/0.64  fof(f652,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f651])).
% 2.12/0.64  fof(f651,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k2_struct_0(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_22 | ~spl6_24 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(forward_demodulation,[],[f650,f214])).
% 2.12/0.64  fof(f214,plain,(
% 2.12/0.64    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_24),
% 2.12/0.64    inference(avatar_component_clause,[],[f213])).
% 2.12/0.64  fof(f650,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_22 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f649])).
% 2.12/0.64  fof(f649,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_22 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(forward_demodulation,[],[f648,f207])).
% 2.12/0.64  fof(f207,plain,(
% 2.12/0.64    k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_22),
% 2.12/0.64    inference(avatar_component_clause,[],[f206])).
% 2.12/0.64  fof(f648,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f647])).
% 2.12/0.64  fof(f647,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_26 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(forward_demodulation,[],[f646,f349])).
% 2.12/0.64  fof(f349,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | (~spl6_26 | ~spl6_37)),
% 2.12/0.64    inference(resolution,[],[f310,f243])).
% 2.12/0.64  fof(f310,plain,(
% 2.12/0.64    m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_37),
% 2.12/0.64    inference(avatar_component_clause,[],[f309])).
% 2.12/0.64  fof(f646,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_7 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(superposition,[],[f65,f634])).
% 2.12/0.64  fof(f634,plain,(
% 2.12/0.64    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | (~spl6_7 | ~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(forward_demodulation,[],[f387,f350])).
% 2.12/0.64  fof(f350,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | (~spl6_7 | ~spl6_37)),
% 2.12/0.64    inference(resolution,[],[f310,f106])).
% 2.12/0.64  fof(f106,plain,(
% 2.12/0.64    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))) ) | ~spl6_7),
% 2.12/0.64    inference(avatar_component_clause,[],[f105])).
% 2.12/0.64  fof(f387,plain,(
% 2.12/0.64    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | (~spl6_37 | ~spl6_41)),
% 2.12/0.64    inference(resolution,[],[f343,f310])).
% 2.12/0.64  fof(f65,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v2_struct_0(X0) | v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f30])).
% 2.12/0.64  fof(f609,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_81 | ~spl6_59),
% 2.12/0.64    inference(avatar_split_clause,[],[f601,f466,f607,f113,f186])).
% 2.12/0.64  fof(f466,plain,(
% 2.12/0.64    spl6_59 <=> ! [X0] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 2.12/0.64  fof(f601,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_59),
% 2.12/0.64    inference(resolution,[],[f467,f71])).
% 2.12/0.64  fof(f467,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0))) ) | ~spl6_59),
% 2.12/0.64    inference(avatar_component_clause,[],[f466])).
% 2.12/0.64  fof(f582,plain,(
% 2.12/0.64    ~spl6_14 | ~spl6_30 | ~spl6_29 | ~spl6_15 | ~spl6_13 | spl6_77),
% 2.12/0.64    inference(avatar_split_clause,[],[f581,f578,f150,f156,f263,f266,f153])).
% 2.12/0.64  fof(f581,plain,(
% 2.12/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_77),
% 2.12/0.64    inference(resolution,[],[f579,f123])).
% 2.12/0.64  fof(f123,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) | ~v1_funct_1(k2_tops_2(X1,X2,X0)) | ~v1_funct_2(X0,X1,X2)) )),
% 2.12/0.64    inference(resolution,[],[f76,f74])).
% 2.12/0.64  fof(f74,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f36])).
% 2.12/0.64  fof(f579,plain,(
% 2.12/0.64    ~v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | spl6_77),
% 2.12/0.64    inference(avatar_component_clause,[],[f578])).
% 2.12/0.64  fof(f534,plain,(
% 2.12/0.64    spl6_23 | ~spl6_38 | ~spl6_34 | ~spl6_15 | ~spl6_14 | spl6_70 | spl6_10 | ~spl6_42),
% 2.12/0.64    inference(avatar_split_clause,[],[f530,f346,f130,f532,f153,f156,f288,f312,f209])).
% 2.12/0.64  fof(f346,plain,(
% 2.12/0.64    spl6_42 <=> ! [X1,X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.12/0.64  fof(f530,plain,(
% 2.12/0.64    v5_pre_topc(sK2,sK0,sK1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,sK1,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_42),
% 2.12/0.64    inference(resolution,[],[f347,f45])).
% 2.12/0.64  fof(f347,plain,(
% 2.12/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_42),
% 2.12/0.64    inference(avatar_component_clause,[],[f346])).
% 2.12/0.64  fof(f515,plain,(
% 2.12/0.64    spl6_10 | ~spl6_19 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_34 | ~spl6_38 | spl6_23 | ~spl6_8 | ~spl6_67 | ~spl6_66),
% 2.12/0.64    inference(avatar_split_clause,[],[f509,f504,f513,f113,f209,f312,f288,f156,f153,f150,f186,f130])).
% 2.12/0.64  fof(f509,plain,(
% 2.12/0.64    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(sK2,sK0,sK1) | ~spl6_66),
% 2.12/0.64    inference(superposition,[],[f72,f505])).
% 2.12/0.64  fof(f72,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f32])).
% 2.12/0.64  fof(f506,plain,(
% 2.12/0.64    spl6_23 | ~spl6_38 | ~spl6_34 | ~spl6_15 | ~spl6_14 | spl6_66 | spl6_10 | ~spl6_21),
% 2.12/0.64    inference(avatar_split_clause,[],[f373,f200,f130,f504,f153,f156,f288,f312,f209])).
% 2.12/0.64  fof(f200,plain,(
% 2.12/0.64    spl6_21 <=> ! [X1,X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.12/0.64  fof(f373,plain,(
% 2.12/0.64    v5_pre_topc(sK2,sK0,sK1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_21),
% 2.12/0.64    inference(resolution,[],[f201,f45])).
% 2.12/0.64  fof(f201,plain,(
% 2.12/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X2,sK0,X1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_21),
% 2.12/0.64    inference(avatar_component_clause,[],[f200])).
% 2.12/0.64  fof(f472,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_60 | ~spl6_31),
% 2.12/0.64    inference(avatar_split_clause,[],[f464,f270,f470,f113,f186])).
% 2.12/0.64  fof(f270,plain,(
% 2.12/0.64    spl6_31 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1))),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.12/0.64  fof(f464,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK5(sK0,X1,X2)) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_31),
% 2.12/0.64    inference(resolution,[],[f271,f71])).
% 2.12/0.64  fof(f271,plain,(
% 2.12/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1)) ) | ~spl6_31),
% 2.12/0.64    inference(avatar_component_clause,[],[f270])).
% 2.12/0.64  fof(f468,plain,(
% 2.12/0.64    ~spl6_8 | spl6_59 | ~spl6_31),
% 2.12/0.64    inference(avatar_split_clause,[],[f462,f270,f466,f113])).
% 2.12/0.64  fof(f462,plain,(
% 2.12/0.64    ( ! [X0] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl6_31),
% 2.12/0.64    inference(resolution,[],[f271,f73])).
% 2.12/0.64  fof(f73,plain,(
% 2.12/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f34])).
% 2.12/0.64  fof(f34,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f33])).
% 2.12/0.64  fof(f33,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f1])).
% 2.12/0.64  fof(f1,axiom,(
% 2.12/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.12/0.64  fof(f396,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_49 | ~spl6_41),
% 2.12/0.64    inference(avatar_split_clause,[],[f388,f342,f394,f113,f186])).
% 2.12/0.64  fof(f388,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK5(sK0,X1,X2))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_41),
% 2.12/0.64    inference(resolution,[],[f343,f71])).
% 2.12/0.64  fof(f348,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_42 | ~spl6_26),
% 2.12/0.64    inference(avatar_split_clause,[],[f340,f242,f346,f113,f186])).
% 2.12/0.64  fof(f340,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK5(sK0,X1,X2)) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_26),
% 2.12/0.64    inference(resolution,[],[f243,f71])).
% 2.12/0.64  fof(f344,plain,(
% 2.12/0.64    ~spl6_8 | spl6_41 | ~spl6_26),
% 2.12/0.64    inference(avatar_split_clause,[],[f339,f242,f342,f113])).
% 2.12/0.64  fof(f339,plain,(
% 2.12/0.64    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl6_26),
% 2.12/0.64    inference(resolution,[],[f243,f73])).
% 2.12/0.64  fof(f328,plain,(
% 2.12/0.64    ~spl6_15 | ~spl6_13 | ~spl6_14 | spl6_28),
% 2.12/0.64    inference(avatar_split_clause,[],[f327,f260,f153,f150,f156])).
% 2.12/0.64  fof(f327,plain,(
% 2.12/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_28),
% 2.12/0.64    inference(resolution,[],[f261,f76])).
% 2.12/0.64  fof(f261,plain,(
% 2.12/0.64    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl6_28),
% 2.12/0.64    inference(avatar_component_clause,[],[f260])).
% 2.12/0.64  fof(f321,plain,(
% 2.12/0.64    ~spl6_15 | ~spl6_13 | ~spl6_14 | spl6_29),
% 2.12/0.64    inference(avatar_split_clause,[],[f320,f263,f153,f150,f156])).
% 2.12/0.64  fof(f320,plain,(
% 2.12/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_29),
% 2.12/0.64    inference(resolution,[],[f264,f75])).
% 2.12/0.64  fof(f264,plain,(
% 2.12/0.64    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl6_29),
% 2.12/0.64    inference(avatar_component_clause,[],[f263])).
% 2.12/0.64  fof(f318,plain,(
% 2.12/0.64    spl6_30),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f317])).
% 2.12/0.64  fof(f317,plain,(
% 2.12/0.64    $false | spl6_30),
% 2.12/0.64    inference(resolution,[],[f267,f122])).
% 2.12/0.64  fof(f122,plain,(
% 2.12/0.64    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.12/0.64    inference(global_subsumption,[],[f43,f44,f121])).
% 2.12/0.64  fof(f121,plain,(
% 2.12/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 2.12/0.64    inference(resolution,[],[f74,f45])).
% 2.12/0.64  fof(f44,plain,(
% 2.12/0.64    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f43,plain,(
% 2.12/0.64    v1_funct_1(sK2)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f267,plain,(
% 2.12/0.64    ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl6_30),
% 2.12/0.64    inference(avatar_component_clause,[],[f266])).
% 2.12/0.64  fof(f316,plain,(
% 2.12/0.64    spl6_38),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f315])).
% 2.12/0.64  fof(f315,plain,(
% 2.12/0.64    $false | spl6_38),
% 2.12/0.64    inference(resolution,[],[f313,f47])).
% 2.12/0.64  fof(f47,plain,(
% 2.12/0.64    v2_pre_topc(sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f313,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | spl6_38),
% 2.12/0.64    inference(avatar_component_clause,[],[f312])).
% 2.12/0.64  fof(f314,plain,(
% 2.12/0.64    spl6_35 | spl6_37 | ~spl6_11 | spl6_23 | ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_8 | ~spl6_19 | ~spl6_34 | ~spl6_38 | ~spl6_22 | ~spl6_24),
% 2.12/0.64    inference(avatar_split_clause,[],[f307,f213,f206,f312,f288,f186,f113,f266,f263,f260,f209,f144,f309,f294])).
% 2.12/0.64  fof(f307,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_22 | ~spl6_24)),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f306])).
% 2.12/0.64  fof(f306,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_22 | ~spl6_24)),
% 2.12/0.64    inference(forward_demodulation,[],[f304,f207])).
% 2.12/0.64  fof(f304,plain,(
% 2.12/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_24),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f303])).
% 2.12/0.64  fof(f303,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k2_struct_0(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_24),
% 2.12/0.64    inference(superposition,[],[f64,f214])).
% 2.12/0.64  fof(f64,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | v2_struct_0(X0) | ~v2_funct_1(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f30])).
% 2.12/0.64  fof(f301,plain,(
% 2.12/0.64    spl6_34),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f300])).
% 2.12/0.64  fof(f300,plain,(
% 2.12/0.64    $false | spl6_34),
% 2.12/0.64    inference(resolution,[],[f289,f48])).
% 2.12/0.64  fof(f48,plain,(
% 2.12/0.64    l1_pre_topc(sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f289,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | spl6_34),
% 2.12/0.64    inference(avatar_component_clause,[],[f288])).
% 2.12/0.64  fof(f290,plain,(
% 2.12/0.64    spl6_1 | ~spl6_33 | ~spl6_10 | ~spl6_2 | ~spl6_8 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_34 | ~spl6_3 | ~spl6_4),
% 2.12/0.64    inference(avatar_split_clause,[],[f282,f89,f85,f288,f156,f153,f150,f113,f81,f130,f284,f78])).
% 2.12/0.64  fof(f81,plain,(
% 2.12/0.64    spl6_2 <=> v2_funct_1(sK2)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.12/0.64  fof(f85,plain,(
% 2.12/0.64    spl6_3 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.12/0.64  fof(f89,plain,(
% 2.12/0.64    spl6_4 <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.12/0.64  fof(f282,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | (~spl6_3 | ~spl6_4)),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f281])).
% 2.12/0.64  fof(f281,plain,(
% 2.12/0.64    k2_struct_0(sK0) != k2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | (~spl6_3 | ~spl6_4)),
% 2.12/0.64    inference(forward_demodulation,[],[f280,f90])).
% 2.12/0.64  fof(f90,plain,(
% 2.12/0.64    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | ~spl6_4),
% 2.12/0.64    inference(avatar_component_clause,[],[f89])).
% 2.12/0.64  fof(f280,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | ~spl6_3),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f277])).
% 2.12/0.64  fof(f277,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | ~spl6_3),
% 2.12/0.64    inference(superposition,[],[f62,f86])).
% 2.12/0.64  fof(f86,plain,(
% 2.12/0.64    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl6_3),
% 2.12/0.64    inference(avatar_component_clause,[],[f85])).
% 2.12/0.64  fof(f62,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_funct_1(X2) | ~v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f26])).
% 2.12/0.64  fof(f272,plain,(
% 2.12/0.64    ~spl6_11 | ~spl6_16 | spl6_31 | ~spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_12 | ~spl6_24),
% 2.12/0.64    inference(avatar_split_clause,[],[f253,f213,f147,f266,f263,f260,f270,f159,f144])).
% 2.12/0.64  fof(f159,plain,(
% 2.12/0.64    spl6_16 <=> l1_struct_0(sK1)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.12/0.64  fof(f147,plain,(
% 2.12/0.64    spl6_12 <=> l1_struct_0(sK0)),
% 2.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.12/0.64  fof(f253,plain,(
% 2.12/0.64    ( ! [X1] : (~l1_struct_0(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1)) ) | ~spl6_24),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f246])).
% 2.12/0.64  fof(f246,plain,(
% 2.12/0.64    ( ! [X1] : (k2_struct_0(sK0) != k2_struct_0(sK0) | ~l1_struct_0(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),X1)) ) | ~spl6_24),
% 2.12/0.64    inference(superposition,[],[f52,f214])).
% 2.12/0.64  fof(f52,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f19])).
% 2.12/0.64  fof(f19,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(flattening,[],[f18])).
% 2.12/0.64  fof(f18,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f9])).
% 2.12/0.64  fof(f9,axiom,(
% 2.12/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 2.12/0.64  fof(f244,plain,(
% 2.12/0.64    ~spl6_2 | ~spl6_12 | spl6_26 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f240,f85,f159,f156,f153,f150,f242,f147,f81])).
% 2.12/0.64  fof(f240,plain,(
% 2.12/0.64    ( ! [X0] : (~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_3),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f239])).
% 2.12/0.64  fof(f239,plain,(
% 2.12/0.64    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_3),
% 2.12/0.64    inference(superposition,[],[f53,f86])).
% 2.12/0.64  fof(f53,plain,(
% 2.12/0.64    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f21])).
% 2.12/0.64  fof(f21,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(flattening,[],[f20])).
% 2.12/0.64  fof(f20,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f8])).
% 2.12/0.64  fof(f8,axiom,(
% 2.12/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).
% 2.12/0.64  fof(f238,plain,(
% 2.12/0.64    ~spl6_19 | ~spl6_8 | spl6_21 | ~spl6_7),
% 2.12/0.64    inference(avatar_split_clause,[],[f236,f105,f200,f113,f186])).
% 2.12/0.64  fof(f236,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_7),
% 2.12/0.64    inference(resolution,[],[f106,f71])).
% 2.12/0.64  fof(f225,plain,(
% 2.12/0.64    ~spl6_23),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f224])).
% 2.12/0.64  fof(f224,plain,(
% 2.12/0.64    $false | ~spl6_23),
% 2.12/0.64    inference(resolution,[],[f210,f46])).
% 2.12/0.64  fof(f46,plain,(
% 2.12/0.64    ~v2_struct_0(sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f210,plain,(
% 2.12/0.64    v2_struct_0(sK1) | ~spl6_23),
% 2.12/0.64    inference(avatar_component_clause,[],[f209])).
% 2.12/0.64  fof(f223,plain,(
% 2.12/0.64    ~spl6_1 | spl6_2),
% 2.12/0.64    inference(avatar_split_clause,[],[f222,f81,f78])).
% 2.12/0.64  fof(f222,plain,(
% 2.12/0.64    v2_funct_1(sK2) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(global_subsumption,[],[f43,f48,f50,f44,f124])).
% 2.12/0.64  fof(f124,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_funct_1(sK2) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(resolution,[],[f59,f45])).
% 2.12/0.64  fof(f59,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f26])).
% 2.12/0.64  fof(f50,plain,(
% 2.12/0.64    l1_pre_topc(sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f221,plain,(
% 2.12/0.64    spl6_13),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f220])).
% 2.12/0.64  fof(f220,plain,(
% 2.12/0.64    $false | spl6_13),
% 2.12/0.64    inference(resolution,[],[f151,f45])).
% 2.12/0.64  fof(f151,plain,(
% 2.12/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_13),
% 2.12/0.64    inference(avatar_component_clause,[],[f150])).
% 2.12/0.64  fof(f219,plain,(
% 2.12/0.64    spl6_14),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f218])).
% 2.12/0.64  fof(f218,plain,(
% 2.12/0.64    $false | spl6_14),
% 2.12/0.64    inference(resolution,[],[f154,f44])).
% 2.12/0.64  fof(f154,plain,(
% 2.12/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_14),
% 2.12/0.64    inference(avatar_component_clause,[],[f153])).
% 2.12/0.64  fof(f215,plain,(
% 2.12/0.64    spl6_24 | ~spl6_2 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_23 | ~spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f168,f85,f209,f159,f156,f153,f150,f147,f81,f213])).
% 2.12/0.64  fof(f168,plain,(
% 2.12/0.64    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f167])).
% 2.12/0.64  fof(f167,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(superposition,[],[f55,f86])).
% 2.12/0.64  fof(f55,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f23])).
% 2.12/0.64  fof(f23,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(flattening,[],[f22])).
% 2.12/0.64  fof(f22,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f6])).
% 2.12/0.64  fof(f6,axiom,(
% 2.12/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 2.12/0.64  fof(f211,plain,(
% 2.12/0.64    spl6_22 | ~spl6_2 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_23 | ~spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f164,f85,f209,f159,f156,f153,f150,f147,f81,f206])).
% 2.12/0.64  fof(f164,plain,(
% 2.12/0.64    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f163])).
% 2.12/0.64  fof(f163,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(superposition,[],[f54,f86])).
% 2.12/0.64  fof(f54,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f23])).
% 2.12/0.64  fof(f204,plain,(
% 2.12/0.64    spl6_16),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f203])).
% 2.12/0.64  fof(f203,plain,(
% 2.12/0.64    $false | spl6_16),
% 2.12/0.64    inference(resolution,[],[f169,f48])).
% 2.12/0.64  fof(f169,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | spl6_16),
% 2.12/0.64    inference(resolution,[],[f160,f56])).
% 2.12/0.64  fof(f56,plain,(
% 2.12/0.64    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f24])).
% 2.12/0.64  fof(f24,plain,(
% 2.12/0.64    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f2])).
% 2.12/0.64  fof(f2,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.12/0.64  fof(f160,plain,(
% 2.12/0.64    ~l1_struct_0(sK1) | spl6_16),
% 2.12/0.64    inference(avatar_component_clause,[],[f159])).
% 2.12/0.64  fof(f195,plain,(
% 2.12/0.64    spl6_12),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f194])).
% 2.12/0.64  fof(f194,plain,(
% 2.12/0.64    $false | spl6_12),
% 2.12/0.64    inference(resolution,[],[f162,f50])).
% 2.12/0.64  fof(f162,plain,(
% 2.12/0.64    ~l1_pre_topc(sK0) | spl6_12),
% 2.12/0.64    inference(resolution,[],[f148,f56])).
% 2.12/0.64  fof(f148,plain,(
% 2.12/0.64    ~l1_struct_0(sK0) | spl6_12),
% 2.12/0.64    inference(avatar_component_clause,[],[f147])).
% 2.12/0.64  fof(f193,plain,(
% 2.12/0.64    spl6_19),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f192])).
% 2.12/0.64  fof(f192,plain,(
% 2.12/0.64    $false | spl6_19),
% 2.12/0.64    inference(resolution,[],[f187,f49])).
% 2.12/0.64  fof(f49,plain,(
% 2.12/0.64    v2_pre_topc(sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f187,plain,(
% 2.12/0.64    ~v2_pre_topc(sK0) | spl6_19),
% 2.12/0.64    inference(avatar_component_clause,[],[f186])).
% 2.12/0.64  fof(f166,plain,(
% 2.12/0.64    spl6_15),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f165])).
% 2.12/0.64  fof(f165,plain,(
% 2.12/0.64    $false | spl6_15),
% 2.12/0.64    inference(resolution,[],[f157,f43])).
% 2.12/0.64  fof(f157,plain,(
% 2.12/0.64    ~v1_funct_1(sK2) | spl6_15),
% 2.12/0.64    inference(avatar_component_clause,[],[f156])).
% 2.12/0.64  fof(f161,plain,(
% 2.12/0.64    spl6_11 | ~spl6_2 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | ~spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f142,f85,f159,f156,f153,f150,f147,f81,f144])).
% 2.12/0.64  fof(f142,plain,(
% 2.12/0.64    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(trivial_inequality_removal,[],[f141])).
% 2.12/0.64  fof(f141,plain,(
% 2.12/0.64    k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_3),
% 2.12/0.64    inference(superposition,[],[f51,f86])).
% 2.12/0.64  fof(f51,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f17])).
% 2.12/0.64  fof(f17,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(flattening,[],[f16])).
% 2.12/0.64  fof(f16,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f7])).
% 2.12/0.64  fof(f7,axiom,(
% 2.12/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 2.12/0.64  fof(f140,plain,(
% 2.12/0.64    ~spl6_1 | spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f139,f85,f78])).
% 2.12/0.64  fof(f139,plain,(
% 2.12/0.64    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(global_subsumption,[],[f43,f48,f50,f44,f137])).
% 2.12/0.64  fof(f137,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(resolution,[],[f58,f45])).
% 2.12/0.64  fof(f58,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f26])).
% 2.12/0.64  fof(f136,plain,(
% 2.12/0.64    ~spl6_1 | spl6_4),
% 2.12/0.64    inference(avatar_split_clause,[],[f135,f89,f78])).
% 2.12/0.64  fof(f135,plain,(
% 2.12/0.64    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(global_subsumption,[],[f43,f48,f50,f44,f133])).
% 2.12/0.64  fof(f133,plain,(
% 2.12/0.64    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(resolution,[],[f57,f45])).
% 2.12/0.64  fof(f57,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f26])).
% 2.12/0.64  fof(f120,plain,(
% 2.12/0.64    spl6_8),
% 2.12/0.64    inference(avatar_contradiction_clause,[],[f119])).
% 2.12/0.64  fof(f119,plain,(
% 2.12/0.64    $false | spl6_8),
% 2.12/0.64    inference(resolution,[],[f114,f50])).
% 2.12/0.64  fof(f114,plain,(
% 2.12/0.64    ~l1_pre_topc(sK0) | spl6_8),
% 2.12/0.64    inference(avatar_component_clause,[],[f113])).
% 2.12/0.64  fof(f107,plain,(
% 2.12/0.64    spl6_1 | spl6_7),
% 2.12/0.64    inference(avatar_split_clause,[],[f37,f105,f78])).
% 2.12/0.64  fof(f37,plain,(
% 2.12/0.64    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) | v3_tops_2(sK2,sK0,sK1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f103,plain,(
% 2.12/0.64    ~spl6_1 | spl6_6 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.12/0.64    inference(avatar_split_clause,[],[f38,f89,f85,f81,f101,f78])).
% 2.12/0.64  fof(f38,plain,(
% 2.12/0.64    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f99,plain,(
% 2.12/0.64    ~spl6_1 | ~spl6_5 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.12/0.64    inference(avatar_split_clause,[],[f39,f89,f85,f81,f94,f78])).
% 2.12/0.64  fof(f39,plain,(
% 2.12/0.64    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f91,plain,(
% 2.12/0.64    spl6_1 | spl6_4),
% 2.12/0.64    inference(avatar_split_clause,[],[f40,f89,f78])).
% 2.12/0.64  fof(f40,plain,(
% 2.12/0.64    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f87,plain,(
% 2.12/0.64    spl6_1 | spl6_3),
% 2.12/0.64    inference(avatar_split_clause,[],[f41,f85,f78])).
% 2.12/0.64  fof(f41,plain,(
% 2.12/0.64    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f83,plain,(
% 2.12/0.64    spl6_1 | spl6_2),
% 2.12/0.64    inference(avatar_split_clause,[],[f42,f81,f78])).
% 2.12/0.64  fof(f42,plain,(
% 2.12/0.64    v2_funct_1(sK2) | v3_tops_2(sK2,sK0,sK1)),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  % SZS output end Proof for theBenchmark
% 2.12/0.64  % (21970)------------------------------
% 2.12/0.64  % (21970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (21970)Termination reason: Refutation
% 2.12/0.64  
% 2.12/0.64  % (21970)Memory used [KB]: 12025
% 2.12/0.64  % (21970)Time elapsed: 0.222 s
% 2.12/0.64  % (21970)------------------------------
% 2.12/0.64  % (21970)------------------------------
% 2.12/0.65  % (21957)Success in time 0.284 s
%------------------------------------------------------------------------------
