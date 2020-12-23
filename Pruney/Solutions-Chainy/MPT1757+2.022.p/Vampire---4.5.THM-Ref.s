%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 539 expanded)
%              Number of leaves         :   45 ( 244 expanded)
%              Depth                    :   21
%              Number of atoms          : 1410 (5969 expanded)
%              Number of equality atoms :   43 ( 355 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f150,f155,f162,f167,f179,f181,f192,f209,f219,f224,f234,f239,f248,f258,f265,f270,f277,f296])).

fof(f296,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f294,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f294,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f293,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f293,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f292,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f292,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f291,f103])).

fof(f103,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f291,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f290,f108])).

fof(f108,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl8_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f290,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f289,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f288,f118])).

fof(f118,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f288,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f287,f154])).

fof(f154,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_14
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f287,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f286,f166])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f286,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f285,f123])).

fof(f123,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f285,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f284,f133])).

fof(f133,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_10
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f284,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f283,f143])).

fof(f143,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl8_12
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_13
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f282,f149])).

fof(f149,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_13
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f282,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f280,f174])).

fof(f174,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_17
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f280,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_18 ),
    inference(resolution,[],[f177,f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f177,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_18
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f277,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | spl8_17
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17
    | ~ spl8_18
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f275,f178])).

fof(f178,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f275,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_12
    | ~ spl8_13
    | spl8_17
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f274,f143])).

fof(f274,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_13
    | spl8_17
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f272,f173])).

fof(f173,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f272,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl8_13
    | ~ spl8_29 ),
    inference(resolution,[],[f257,f149])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl8_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f270,plain,
    ( ~ spl8_15
    | spl8_30 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl8_15
    | spl8_30 ),
    inference(subsumption_resolution,[],[f267,f161])).

fof(f161,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_15
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f267,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_30 ),
    inference(resolution,[],[f264,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f264,plain,
    ( ~ l1_struct_0(sK3)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_30
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f265,plain,
    ( ~ spl8_30
    | spl8_8
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f260,f252,f121,f262])).

fof(f252,plain,
    ( spl8_28
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f260,plain,
    ( ~ l1_struct_0(sK3)
    | spl8_8
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f259,f123])).

fof(f259,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_28 ),
    inference(resolution,[],[f254,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f254,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f258,plain,
    ( spl8_28
    | spl8_29
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f250,f246,f256,f252])).

fof(f246,plain,
    ( spl8_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | v1_xboole_0(u1_struct_0(sK3)) )
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | v1_xboole_0(u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl8_27 ),
    inference(resolution,[],[f247,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl8_27
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f244,f237,f164,f152,f96,f91,f86,f246])).

fof(f237,plain,
    ( spl8_26
  <=> ! [X1,X0] :
        ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK1,X0,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f243,f88])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f242,f93])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl8_3
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f241,f98])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f240,f166])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(resolution,[],[f238,f154])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK1,X0,sK2,X1) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl8_26
    | ~ spl8_7
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f235,f232,f116,f237])).

fof(f232,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ r2_hidden(X1,u1_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK1,X0,sK2,X1) )
    | ~ spl8_7
    | ~ spl8_25 ),
    inference(resolution,[],[f233,f118])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f234,plain,
    ( spl8_25
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f230,f222,f131,f121,f111,f106,f101,f232])).

fof(f222,plain,
    ( spl8_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | sP6(sK3,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f229,f103])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f228,f108])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | ~ spl8_6
    | spl8_8
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f227,f113])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | spl8_8
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f226,f123])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f225,f133])).

fof(f225,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_pre_topc(sK3,sK1)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(sK1,X1,X2,X0) )
    | ~ spl8_24 ),
    inference(resolution,[],[f223,f81])).

fof(f81,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(general_splitting,[],[f73,f80_D])).

fof(f80,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ v3_pre_topc(X4,X1)
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | sP6(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f80_D])).

fof(f80_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ v3_pre_topc(X4,X1)
          | ~ r2_hidden(X6,X4)
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
    <=> ~ sP6(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f223,plain,
    ( ! [X0] :
        ( sP6(sK3,sK1,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3)) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl8_24
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f220,f217,f222])).

fof(f217,plain,
    ( spl8_23
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK3))
        | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
        | sP6(X3,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | sP6(sK3,sK1,X0) )
    | ~ spl8_23 ),
    inference(resolution,[],[f218,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f218,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
        | ~ r2_hidden(X2,u1_struct_0(sK3))
        | sP6(X3,sK1,X2) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl8_23
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f211,f197,f189,f217])).

fof(f189,plain,
    ( spl8_19
  <=> v3_pre_topc(u1_struct_0(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f197,plain,
    ( spl8_20
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f211,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(sK3))
        | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
        | sP6(X3,sK1,X2) )
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f195,f198])).

fof(f198,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f195,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(sK3))
        | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X3))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | sP6(X3,sK1,X2) )
    | ~ spl8_19 ),
    inference(resolution,[],[f191,f80])).

fof(f191,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f209,plain,
    ( ~ spl8_6
    | ~ spl8_10
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_10
    | spl8_20 ),
    inference(subsumption_resolution,[],[f207,f113])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_10
    | spl8_20 ),
    inference(subsumption_resolution,[],[f205,f133])).

fof(f205,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl8_20 ),
    inference(resolution,[],[f199,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f199,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f192,plain,
    ( spl8_19
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f187,f131,f126,f111,f106,f189])).

fof(f126,plain,
    ( spl8_9
  <=> v1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f187,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f186,f108])).

fof(f186,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f185,f113])).

fof(f185,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f184,f133])).

fof(f184,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_9 ),
    inference(resolution,[],[f183,f128])).

fof(f128,plain,
    ( v1_tsep_1(sK3,sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f84,f60])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f181,plain,
    ( ~ spl8_17
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f180,f176,f136,f172])).

fof(f136,plain,
    ( spl8_11
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f180,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f170,f178])).

fof(f170,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f57,f138])).

fof(f138,plain,
    ( sK4 = sK5
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f57,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f34,f33,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK0,X2,X4) )
                        & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | r1_tmap_1(X1,sK0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                      & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | r1_tmap_1(sK1,sK0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_pre_topc(X3,sK1)
              & v1_tsep_1(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                    & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | r1_tmap_1(sK1,sK0,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_pre_topc(X3,sK1)
            & v1_tsep_1(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                  & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | r1_tmap_1(sK1,sK0,sK2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_pre_topc(X3,sK1)
          & v1_tsep_1(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | r1_tmap_1(sK1,sK0,sK2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_pre_topc(X3,sK1)
        & v1_tsep_1(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
              & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | r1_tmap_1(sK1,sK0,sK2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_pre_topc(sK3,sK1)
      & v1_tsep_1(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
            & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | r1_tmap_1(sK1,sK0,sK2,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
          & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | r1_tmap_1(sK1,sK0,sK2,sK4) )
          & sK4 = X5
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
        & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | r1_tmap_1(sK1,sK0,sK2,sK4) )
        & sK4 = X5
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
      & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
      & sK4 = sK5
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f179,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f169,f136,f176,f172])).

fof(f169,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f56,f138])).

fof(f56,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f167,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f49,f164])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f162,plain,
    ( spl8_15
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f157,f131,f111,f159])).

fof(f157,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f156,f113])).

fof(f156,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f59,f133])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f155,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f48,f152])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f150,plain,
    ( spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f145,f136,f147])).

fof(f145,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f54,f138])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f144,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f53,f141])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f139,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f55,f136])).

fof(f55,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f52,f131])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f129,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f51,f126])).

fof(f51,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f124,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f50,f121])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:30:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (5066)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (5060)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (5078)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (5061)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (5068)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (5060)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f150,f155,f162,f167,f179,f181,f192,f209,f219,f224,f234,f239,f248,f258,f265,f270,f277,f296])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl8_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    v2_struct_0(sK0) | (~spl8_2 | ~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    v2_pre_topc(sK0) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl8_2 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_3 | spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f292,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl8_3 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f291,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl8_4 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f290,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v2_pre_topc(sK1) | ~spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl8_5 <=> v2_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f289,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    l1_pre_topc(sK1) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl8_6 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_7 | spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f288,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl8_7 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_14 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f287,f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl8_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl8_14 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_16 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f286,f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl8_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl8_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~v2_struct_0(sK3) | spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl8_8 <=> v2_struct_0(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_10 | ~spl8_12 | ~spl8_13 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f284,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl8_10 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_13 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl8_12 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_13 | ~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f282,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl8_13 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_17 | spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl8_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    spl8_17 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_18),
% 0.21/0.50    inference(resolution,[],[f177,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl8_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f176])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl8_18 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ~spl8_12 | ~spl8_13 | spl8_17 | ~spl8_18 | ~spl8_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    $false | (~spl8_12 | ~spl8_13 | spl8_17 | ~spl8_18 | ~spl8_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f275,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl8_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f176])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl8_12 | ~spl8_13 | spl8_17 | ~spl8_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f274,f143])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl8_13 | spl8_17 | ~spl8_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f272,f173])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl8_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f172])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | (~spl8_13 | ~spl8_29)),
% 0.21/0.50    inference(resolution,[],[f257,f149])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)) ) | ~spl8_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f256])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    spl8_29 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ~spl8_15 | spl8_30),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    $false | (~spl8_15 | spl8_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f267,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    l1_pre_topc(sK3) | ~spl8_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl8_15 <=> l1_pre_topc(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | spl8_30),
% 0.21/0.50    inference(resolution,[],[f264,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | spl8_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f262])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl8_30 <=> l1_struct_0(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~spl8_30 | spl8_8 | ~spl8_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f260,f252,f121,f262])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    spl8_28 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | (spl8_8 | ~spl8_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f123])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl8_28),
% 0.21/0.50    inference(resolution,[],[f254,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK3)) | ~spl8_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f252])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl8_28 | spl8_29 | ~spl8_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f250,f246,f256,f252])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    spl8_27 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0) | v1_xboole_0(u1_struct_0(sK3))) ) | ~spl8_27),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f249])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl8_27),
% 0.21/0.50    inference(resolution,[],[f247,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | ~spl8_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f246])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    spl8_27 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_14 | ~spl8_16 | ~spl8_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f244,f237,f164,f152,f96,f91,f86,f246])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    spl8_26 <=> ! [X1,X0] : (~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK1,X0,sK2,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_14 | ~spl8_16 | ~spl8_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f88])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_14 | ~spl8_16 | ~spl8_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f93])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl8_3 | ~spl8_14 | ~spl8_16 | ~spl8_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f241,f98])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl8_14 | ~spl8_16 | ~spl8_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f240,f166])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl8_14 | ~spl8_26)),
% 0.21/0.50    inference(resolution,[],[f238,f154])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK1,X0,sK2,X1)) ) | ~spl8_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f237])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl8_26 | ~spl8_7 | ~spl8_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f235,f232,f116,f237])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl8_25 <=> ! [X1,X0,X2] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tmap_1(sK3,X0,k2_tmap_1(sK1,X0,sK2,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(X0)) | ~r2_hidden(X1,u1_struct_0(sK3)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK1,X0,sK2,X1)) ) | (~spl8_7 | ~spl8_25)),
% 0.21/0.50    inference(resolution,[],[f233,f118])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | ~spl8_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f232])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    spl8_25 | spl8_4 | ~spl8_5 | ~spl8_6 | spl8_8 | ~spl8_10 | ~spl8_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f222,f131,f121,f111,f106,f101,f232])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl8_24 <=> ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | sP6(sK3,sK1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | (spl8_4 | ~spl8_5 | ~spl8_6 | spl8_8 | ~spl8_10 | ~spl8_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f229,f103])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | (~spl8_5 | ~spl8_6 | spl8_8 | ~spl8_10 | ~spl8_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f228,f108])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | (~spl8_6 | spl8_8 | ~spl8_10 | ~spl8_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f227,f113])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | (spl8_8 | ~spl8_10 | ~spl8_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f226,f123])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | (~spl8_10 | ~spl8_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f225,f133])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X1,k2_tmap_1(sK1,X1,X2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | r1_tmap_1(sK1,X1,X2,X0)) ) | ~spl8_24),
% 0.21/0.50    inference(resolution,[],[f223,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X3,X1] : (~sP6(X3,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.50    inference(general_splitting,[],[f73,f80_D])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X6,X4,X3,X1] : (~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | sP6(X3,X1,X6)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f80_D])).
% 0.21/0.50  fof(f80_D,plain,(
% 0.21/0.50    ( ! [X6,X1,X3] : (( ! [X4] : (~v3_pre_topc(X4,X1) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) ) <=> ~sP6(X3,X1,X6)) )),
% 0.21/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0] : (sP6(sK3,sK1,X0) | ~r2_hidden(X0,u1_struct_0(sK3))) ) | ~spl8_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f222])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    spl8_24 | ~spl8_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f220,f217,f222])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl8_23 <=> ! [X3,X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | sP6(X3,sK1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | sP6(sK3,sK1,X0)) ) | ~spl8_23),
% 0.21/0.50    inference(resolution,[],[f218,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | ~r2_hidden(X2,u1_struct_0(sK3)) | sP6(X3,sK1,X2)) ) | ~spl8_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f217])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    spl8_23 | ~spl8_19 | ~spl8_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f211,f197,f189,f217])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    spl8_19 <=> v3_pre_topc(u1_struct_0(sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl8_20 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | sP6(X3,sK1,X2)) ) | (~spl8_19 | ~spl8_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(X3)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | sP6(X3,sK1,X2)) ) | ~spl8_19),
% 0.21/0.50    inference(resolution,[],[f191,f80])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | ~spl8_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f189])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~spl8_6 | ~spl8_10 | spl8_20),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    $false | (~spl8_6 | ~spl8_10 | spl8_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f207,f113])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | (~spl8_10 | spl8_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f133])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl8_20),
% 0.21/0.50    inference(resolution,[],[f199,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl8_19 | ~spl8_5 | ~spl8_6 | ~spl8_9 | ~spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f187,f131,f126,f111,f106,f189])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl8_9 <=> v1_tsep_1(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | (~spl8_5 | ~spl8_6 | ~spl8_9 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f108])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1) | (~spl8_6 | ~spl8_9 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f113])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_9 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f133])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~m1_pre_topc(sK3,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_9),
% 0.21/0.50    inference(resolution,[],[f183,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v1_tsep_1(sK3,sK1) | ~spl8_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f60])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ~spl8_17 | ~spl8_11 | ~spl8_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f176,f136,f172])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl8_11 <=> sK4 = sK5),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ~r1_tmap_1(sK1,sK0,sK2,sK4) | (~spl8_11 | ~spl8_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f178])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl8_11),
% 0.21/0.50    inference(forward_demodulation,[],[f57,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    sK4 = sK5 | ~spl8_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f28,f34,f33,f32,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl8_17 | spl8_18 | ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f169,f136,f176,f172])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl8_11),
% 0.21/0.50    inference(forward_demodulation,[],[f56,f138])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl8_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f164])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl8_15 | ~spl8_6 | ~spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f157,f131,f111,f159])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    l1_pre_topc(sK3) | (~spl8_6 | ~spl8_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f113])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~spl8_10),
% 0.21/0.50    inference(resolution,[],[f59,f133])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl8_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f152])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl8_13 | ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f136,f147])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl8_11),
% 0.21/0.50    inference(forward_demodulation,[],[f54,f138])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl8_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f141])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f136])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    sK4 = sK5),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f131])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl8_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f126])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v1_tsep_1(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f121])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f116])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f111])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f106])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f101])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f96])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f91])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f86])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (5060)------------------------------
% 0.21/0.50  % (5060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5060)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (5060)Memory used [KB]: 6396
% 0.21/0.50  % (5060)Time elapsed: 0.088 s
% 0.21/0.50  % (5060)------------------------------
% 0.21/0.50  % (5060)------------------------------
% 0.21/0.50  % (5057)Success in time 0.133 s
%------------------------------------------------------------------------------
