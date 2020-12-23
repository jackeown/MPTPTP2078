%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 404 expanded)
%              Number of leaves         :   31 ( 139 expanded)
%              Depth                    :   27
%              Number of atoms          : 1329 (3197 expanded)
%              Number of equality atoms :   15 (  98 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f177,f182,f187,f192,f198,f203,f208,f219,f257,f272,f278,f287,f301,f307])).

fof(f307,plain,
    ( spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | spl9_21 ),
    inference(subsumption_resolution,[],[f305,f217])).

fof(f217,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl9_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl9_21
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f305,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f304,f202])).

fof(f202,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl9_18
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f304,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f303,f63])).

fof(f63,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl9_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f303,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(resolution,[],[f299,f118])).

fof(f118,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_12
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f298,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f298,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f297,f186])).

fof(f186,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_15
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f297,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f296,f207])).

fof(f207,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl9_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f295,f197])).

fof(f197,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl9_17
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f294,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f294,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f293,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f292,f78])).

fof(f78,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl9_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f291,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl9_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f291,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f290,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) )
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(resolution,[],[f214,f122])).

fof(f122,plain,
    ( ! [X12,X10,X13,X11] :
        ( ~ r1_tmap_1(X11,X10,sK2,X13)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X10)
        | ~ v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ v2_pre_topc(X10)
        | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13) )
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f68,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f214,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl9_20
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f301,plain,
    ( ~ spl9_11
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f289,f214])).

fof(f289,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_11
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f210,f218])).

fof(f218,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f210,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f23,f113])).

fof(f113,plain,
    ( sK5 = sK6
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_11
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f23,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f287,plain,
    ( ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f285,f103])).

fof(f103,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_9
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f285,plain,
    ( ~ v3_pre_topc(sK4,sK1)
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f284,f181])).

fof(f181,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl9_14
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f284,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(sK4,sK1)
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f282,f191])).

fof(f191,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl9_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f282,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ v3_pre_topc(sK4,sK1)
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(resolution,[],[f267,f108])).

fof(f108,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl9_10
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl9_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(sK5,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ v3_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f278,plain,
    ( ~ spl9_5
    | ~ spl9_12
    | spl9_24 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_12
    | spl9_24 ),
    inference(subsumption_resolution,[],[f276,f83])).

fof(f276,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_12
    | spl9_24 ),
    inference(subsumption_resolution,[],[f274,f118])).

fof(f274,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl9_24 ),
    inference(resolution,[],[f271,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f271,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl9_24 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl9_24
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f272,plain,
    ( spl9_23
    | ~ spl9_24
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_15
    | spl9_22 ),
    inference(avatar_split_clause,[],[f264,f254,f184,f81,f76,f71,f269,f266])).

fof(f254,plain,
    ( spl9_22
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,X0) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_15
    | spl9_22 ),
    inference(subsumption_resolution,[],[f263,f186])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_22 ),
    inference(resolution,[],[f256,f140])).

fof(f140,plain,
    ( ! [X6,X8,X7] :
        ( m1_connsp_2(X7,sK1,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X8,sK1)
        | ~ r1_tarski(X8,X7)
        | ~ r2_hidden(X6,X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK1)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f139,f73])).

fof(f139,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X8,sK1)
        | ~ r1_tarski(X8,X7)
        | ~ r2_hidden(X6,X8)
        | m1_connsp_2(X7,sK1,X6) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f128,f78])).

fof(f128,plain,
    ( ! [X6,X8,X7] :
        ( ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(X8,sK1)
        | ~ r1_tarski(X8,X7)
        | ~ r2_hidden(X6,X8)
        | m1_connsp_2(X7,sK1,X6) )
    | ~ spl9_5 ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f256,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f257,plain,
    ( ~ spl9_22
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f252,f216,f212,f205,f200,f195,f184,f116,f96,f91,f86,f81,f76,f71,f66,f61,f254])).

fof(f252,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f251,f186])).

fof(f251,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(resolution,[],[f248,f224])).

fof(f224,plain,
    ( ! [X14,X13] :
        ( r1_tarski(sK8(sK1,X13,X14),X14)
        | ~ m1_connsp_2(X14,sK1,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f146,f148])).

fof(f148,plain,
    ( ! [X15,X16] :
        ( m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X16,sK1,X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK1)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f147,f73])).

fof(f147,plain,
    ( ! [X15,X16] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X15,u1_struct_0(sK1))
        | ~ m1_connsp_2(X16,sK1,X15)
        | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f132,f78])).

fof(f132,plain,
    ( ! [X15,X16] :
        ( ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X15,u1_struct_0(sK1))
        | ~ m1_connsp_2(X16,sK1,X15)
        | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl9_5 ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f146,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X14,sK1,X13)
        | r1_tarski(sK8(sK1,X13,X14),X14) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f145,f73])).

fof(f145,plain,
    ( ! [X14,X13] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X14,sK1,X13)
        | r1_tarski(sK8(sK1,X13,X14),X14) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f131,f78])).

fof(f131,plain,
    ( ! [X14,X13] :
        ( ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X14,sK1,X13)
        | r1_tarski(sK8(sK1,X13,X14),X14) )
    | ~ spl9_5 ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_tarski(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK8(sK1,sK5,X0),u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f246,f186])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK8(sK1,sK5,X0),u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1)) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(resolution,[],[f245,f230])).

fof(f230,plain,
    ( ! [X10,X9] :
        ( m1_connsp_2(sK8(sK1,X9,X10),sK1,X9)
        | ~ m1_connsp_2(X10,sK1,X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK1)) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f142,f148])).

fof(f142,plain,
    ( ! [X10,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X10,sK1,X9)
        | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9) )
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f141,f73])).

fof(f141,plain,
    ( ! [X10,X9] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X9,u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X10,sK1,X9)
        | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9) )
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f129,f78])).

fof(f129,plain,
    ( ! [X10,X9] :
        ( ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X9,u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X10,sK1,X9)
        | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9) )
    | ~ spl9_5 ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_connsp_2(sK8(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK1,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_20
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f244,f213])).

fof(f213,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f243,f186])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f242,f202])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_21 ),
    inference(resolution,[],[f241,f218])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f240,f63])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ m1_connsp_2(X1,sK1,X0)
        | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(resolution,[],[f239,f118])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f238,f207])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f237,f93])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f236,f88])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f235,f83])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f234,f78])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f233,f73])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f232,f98])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_connsp_2(X2,sK1,X1)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | r1_tmap_1(sK1,sK0,sK2,X1) )
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(resolution,[],[f123,f197])).

fof(f123,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X4,u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X4,u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X2))
        | ~ r1_tarski(X3,u1_struct_0(X2))
        | ~ m1_connsp_2(X3,X1,X4)
        | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4)
        | r1_tmap_1(X1,X0,sK2,X4) )
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f219,plain,
    ( spl9_20
    | spl9_21
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f209,f111,f216,f212])).

fof(f209,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f22,f113])).

fof(f22,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f208,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f35,f205])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f203,plain,
    ( spl9_18
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f193,f174,f111,f200])).

fof(f174,plain,
    ( spl9_13
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f193,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(forward_demodulation,[],[f176,f113])).

fof(f176,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f198,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f34,f195])).

fof(f34,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f192,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f30,f189])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f187,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f29,f184])).

fof(f29,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f182,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f27,f179])).

fof(f27,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f177,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f24,f174])).

fof(f24,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f119,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f32,f116])).

fof(f32,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f28,f111])).

fof(f28,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f26,f106])).

fof(f26,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f25,f101])).

fof(f25,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f99,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (14737)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (14745)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (14735)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14733)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (14743)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (14744)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (14736)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (14734)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (14733)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (14741)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (14750)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f177,f182,f187,f192,f198,f203,f208,f219,f257,f272,f278,f287,f301,f307])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_20 | spl9_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f306])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    $false | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_20 | spl9_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f305,f217])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl9_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl9_21 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f304,f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    spl9_18 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f303,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~v2_struct_0(sK3) | spl9_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl9_1 <=> v2_struct_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.52  fof(f303,plain,(
% 0.21/0.52    v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(resolution,[],[f299,f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK1) | ~spl9_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl9_12 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_15 | ~spl9_17 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f298,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl9_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl9_7 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_15 | ~spl9_17 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f297,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl9_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    spl9_15 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17 | ~spl9_19 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f296,f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl9_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f205])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl9_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f295,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl9_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl9_17 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f294,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl9_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl9_6 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f293,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    l1_pre_topc(sK1) | ~spl9_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl9_5 <=> l1_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f292,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v2_pre_topc(sK1) | ~spl9_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl9_4 <=> v2_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f291,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~v2_struct_0(sK1) | spl9_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl9_3 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | ~spl9_8 | ~spl9_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f290,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl9_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl9_8 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)) ) | (~spl9_2 | ~spl9_20)),
% 0.21/0.52    inference(resolution,[],[f214,f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X12,X10,X13,X11] : (~r1_tmap_1(X11,X10,sK2,X13) | ~l1_pre_topc(X10) | v2_struct_0(X11) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(X10) | ~v1_funct_2(sK2,u1_struct_0(X11),u1_struct_0(X10)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10)))) | v2_struct_0(X12) | ~m1_pre_topc(X12,X11) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~v2_pre_topc(X10) | r1_tmap_1(X12,X10,k2_tmap_1(X11,X10,sK2,X12),X13)) ) | ~spl9_2),
% 0.21/0.52    inference(resolution,[],[f68,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.52    inference(equality_resolution,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl9_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl9_2 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl9_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f212])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl9_20 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    ~spl9_11 | ~spl9_20 | ~spl9_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    $false | (~spl9_11 | ~spl9_20 | ~spl9_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f289,f214])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    ~r1_tmap_1(sK1,sK0,sK2,sK5) | (~spl9_11 | ~spl9_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f210,f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl9_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f216])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl9_11),
% 0.21/0.52    inference(forward_demodulation,[],[f23,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    sK5 = sK6 | ~spl9_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl9_11 <=> sK5 = sK6),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    ~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_16 | ~spl9_23),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    $false | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_16 | ~spl9_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f285,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    v3_pre_topc(sK4,sK1) | ~spl9_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl9_9 <=> v3_pre_topc(sK4,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    ~v3_pre_topc(sK4,sK1) | (~spl9_10 | ~spl9_14 | ~spl9_16 | ~spl9_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f284,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    r1_tarski(sK4,u1_struct_0(sK3)) | ~spl9_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl9_14 <=> r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(sK4,sK1) | (~spl9_10 | ~spl9_16 | ~spl9_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f282,f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl9_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl9_16 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK4,u1_struct_0(sK3)) | ~v3_pre_topc(sK4,sK1) | (~spl9_10 | ~spl9_23)),
% 0.21/0.52    inference(resolution,[],[f267,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    r2_hidden(sK5,sK4) | ~spl9_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl9_10 <=> r2_hidden(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK5,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1)) ) | ~spl9_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f266])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    spl9_23 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ~spl9_5 | ~spl9_12 | spl9_24),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f277])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    $false | (~spl9_5 | ~spl9_12 | spl9_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f276,f83])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | (~spl9_12 | spl9_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f118])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl9_24),
% 0.21/0.52    inference(resolution,[],[f271,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl9_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl9_24 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    spl9_23 | ~spl9_24 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_15 | spl9_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f264,f254,f184,f81,f76,f71,f269,f266])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl9_22 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r2_hidden(sK5,X0)) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_15 | spl9_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f263,f186])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r2_hidden(sK5,X0) | ~m1_subset_1(sK5,u1_struct_0(sK1))) ) | (spl9_3 | ~spl9_4 | ~spl9_5 | spl9_22)),
% 0.21/0.53    inference(resolution,[],[f256,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (m1_connsp_2(X7,sK1,X6) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X8,sK1) | ~r1_tarski(X8,X7) | ~r2_hidden(X6,X8) | ~m1_subset_1(X6,u1_struct_0(sK1))) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f73])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (v2_struct_0(sK1) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X8,sK1) | ~r1_tarski(X8,X7) | ~r2_hidden(X6,X8) | m1_connsp_2(X7,sK1,X6)) ) | (~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f78])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X8,sK1) | ~r1_tarski(X8,X7) | ~r2_hidden(X6,X8) | m1_connsp_2(X7,sK1,X6)) ) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f83,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | spl9_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f254])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ~spl9_22 | spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f252,f216,f212,f205,f200,f195,f184,f116,f96,f91,f86,f81,f76,f71,f66,f61,f254])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f251,f186])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f250])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(resolution,[],[f248,f224])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ( ! [X14,X13] : (r1_tarski(sK8(sK1,X13,X14),X14) | ~m1_connsp_2(X14,sK1,X13) | ~m1_subset_1(X13,u1_struct_0(sK1))) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X15,X16] : (m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X16,sK1,X15) | ~m1_subset_1(X15,u1_struct_0(sK1))) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f73])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X15,X16] : (v2_struct_0(sK1) | ~m1_subset_1(X15,u1_struct_0(sK1)) | ~m1_connsp_2(X16,sK1,X15) | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f78])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X15,X16] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X15,u1_struct_0(sK1)) | ~m1_connsp_2(X16,sK1,X15) | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f83,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X14,X13] : (~m1_subset_1(X13,u1_struct_0(sK1)) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X14,sK1,X13) | r1_tarski(sK8(sK1,X13,X14),X14)) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f73])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X14,X13] : (v2_struct_0(sK1) | ~m1_subset_1(X13,u1_struct_0(sK1)) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X14,sK1,X13) | r1_tarski(sK8(sK1,X13,X14),X14)) ) | (~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f78])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X14,X13] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X13,u1_struct_0(sK1)) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X14,sK1,X13) | r1_tarski(sK8(sK1,X13,X14),X14)) ) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f83,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r1_tarski(sK8(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK8(sK1,sK5,X0),u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f246,f186])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK8(sK1,sK5,X0),u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1))) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(resolution,[],[f245,f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ( ! [X10,X9] : (m1_connsp_2(sK8(sK1,X9,X10),sK1,X9) | ~m1_connsp_2(X10,sK1,X9) | ~m1_subset_1(X9,u1_struct_0(sK1))) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f148])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ( ! [X10,X9] : (~m1_subset_1(X9,u1_struct_0(sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X10,sK1,X9) | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9)) ) | (spl9_3 | ~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f73])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X10,X9] : (v2_struct_0(sK1) | ~m1_subset_1(X9,u1_struct_0(sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X10,sK1,X9) | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9)) ) | (~spl9_4 | ~spl9_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f78])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ( ! [X10,X9] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X9,u1_struct_0(sK1)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X10,sK1,X9) | m1_connsp_2(sK8(sK1,X9,X10),sK1,X9)) ) | ~spl9_5),
% 0.21/0.53    inference(resolution,[],[f83,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | m1_connsp_2(sK8(X0,X1,X2),X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK5) | ~r1_tarski(X0,u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | spl9_20 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f244,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl9_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f212])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_15 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f243,f186])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_18 | ~spl9_19 | ~spl9_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f242,f202])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,sK5)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_21)),
% 0.21/0.53    inference(resolution,[],[f241,f218])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f240,f63])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(sK3) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,X0) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | r1_tmap_1(sK1,sK0,sK2,X0)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_12 | ~spl9_17 | ~spl9_19)),
% 0.21/0.53    inference(resolution,[],[f239,f118])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_17 | ~spl9_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f238,f207])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f237,f93])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f88])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f235,f83])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f78])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | spl9_3 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f233,f73])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | ~spl9_8 | ~spl9_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f232,f98])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_connsp_2(X2,sK1,X1) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) ) | (~spl9_2 | ~spl9_17)),
% 0.21/0.53    inference(resolution,[],[f123,f197])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl9_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f56])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_tarski(X3,u1_struct_0(X2)) | ~m1_connsp_2(X3,X1,X4) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK2,X2),X4) | r1_tmap_1(X1,X0,sK2,X4)) ) | ~spl9_2),
% 0.21/0.53    inference(resolution,[],[f68,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.53    inference(equality_resolution,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    spl9_20 | spl9_21 | ~spl9_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f209,f111,f216,f212])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl9_11),
% 0.21/0.53    inference(forward_demodulation,[],[f22,f113])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl9_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f205])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    spl9_18 | ~spl9_11 | ~spl9_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f174,f111,f200])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    spl9_13 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_11 | ~spl9_13)),
% 0.21/0.53    inference(forward_demodulation,[],[f176,f113])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl9_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f174])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    spl9_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f195])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl9_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f189])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    spl9_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f184])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    spl9_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f27,f179])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    spl9_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f24,f174])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl9_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f116])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl9_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f111])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    sK5 = sK6),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl9_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f26,f106])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    r2_hidden(sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl9_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f101])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v3_pre_topc(sK4,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl9_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f96])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl9_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f91])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~spl9_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f86])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl9_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f81])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl9_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f76])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ~spl9_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f71])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~spl9_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14733)------------------------------
% 0.21/0.53  % (14733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14733)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14733)Memory used [KB]: 10874
% 0.21/0.53  % (14733)Time elapsed: 0.084 s
% 0.21/0.53  % (14733)------------------------------
% 0.21/0.53  % (14733)------------------------------
% 0.21/0.53  % (14742)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (14729)Success in time 0.174 s
%------------------------------------------------------------------------------
