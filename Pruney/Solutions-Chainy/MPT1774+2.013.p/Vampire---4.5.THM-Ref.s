%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 650 expanded)
%              Number of leaves         :   55 ( 361 expanded)
%              Depth                    :   10
%              Number of atoms          : 1360 (10729 expanded)
%              Number of equality atoms :   36 ( 531 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f143,f147,f151,f155,f159,f163,f167,f174,f179,f190,f196,f208,f215,f220,f231,f237,f248,f258,f272,f314,f326,f338,f341,f346,f352,f354])).

fof(f354,plain,
    ( ~ spl8_4
    | ~ spl8_31
    | ~ spl8_33
    | ~ spl8_5
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f353,f350,f93,f229,f223,f89])).

fof(f89,plain,
    ( spl8_4
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f223,plain,
    ( spl8_31
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f229,plain,
    ( spl8_33
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f93,plain,
    ( spl8_5
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f350,plain,
    ( spl8_49
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(sK6,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f353,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_5
    | ~ spl8_49 ),
    inference(resolution,[],[f351,f94])).

fof(f94,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f350])).

fof(f352,plain,
    ( spl8_15
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_8
    | spl8_49
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f348,f330,f350,f105,f203,f200,f133])).

fof(f133,plain,
    ( spl8_15
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f200,plain,
    ( spl8_28
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f203,plain,
    ( spl8_29
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f105,plain,
    ( spl8_8
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f330,plain,
    ( spl8_47
  <=> ! [X1] :
        ( ~ m1_connsp_2(X1,sK3,sK6)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X1,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_47 ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_47 ),
    inference(resolution,[],[f331,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f331,plain,
    ( ! [X1] :
        ( ~ m1_connsp_2(X1,sK3,sK6)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X1,u1_struct_0(sK2)) )
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f330])).

fof(f346,plain,
    ( ~ spl8_14
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f342,f256,f97,f145,f109,f129])).

fof(f129,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f109,plain,
    ( spl8_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f145,plain,
    ( spl8_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f97,plain,
    ( spl8_6
  <=> v3_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f256,plain,
    ( spl8_38
  <=> ! [X0] :
        ( ~ v3_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(resolution,[],[f257,f98])).

fof(f98,plain,
    ( v3_pre_topc(sK5,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK3,X0) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f256])).

fof(f341,plain,
    ( spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_17
    | spl8_15
    | ~ spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_8
    | ~ spl8_25
    | spl8_47
    | ~ spl8_1
    | spl8_24 ),
    inference(avatar_split_clause,[],[f340,f172,f75,f330,f177,f105,f113,f117,f121,f125,f129,f133,f141,f157,f161,f165,f145,f149,f153])).

fof(f153,plain,
    ( spl8_20
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f149,plain,
    ( spl8_19
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f165,plain,
    ( spl8_23
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f161,plain,
    ( spl8_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f157,plain,
    ( spl8_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f141,plain,
    ( spl8_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f125,plain,
    ( spl8_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f121,plain,
    ( spl8_12
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f117,plain,
    ( spl8_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f113,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f177,plain,
    ( spl8_25
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f75,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f172,plain,
    ( spl8_24
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
        | ~ m1_connsp_2(X0,sK3,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK1)
        | v2_struct_0(sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl8_24 ),
    inference(resolution,[],[f337,f169])).

fof(f169,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f73,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
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
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f337,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f172])).

fof(f338,plain,
    ( ~ spl8_24
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f336,f85,f78,f172])).

fof(f78,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f85,plain,
    ( spl8_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f336,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f79,f86])).

fof(f86,plain,
    ( sK6 = sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f326,plain,
    ( ~ spl8_19
    | spl8_20
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_24
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f321,f311,f172,f145,f129,f153,f149])).

fof(f311,plain,
    ( spl8_45
  <=> ! [X0] :
        ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_24
    | ~ spl8_45 ),
    inference(resolution,[],[f312,f173])).

fof(f173,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f172])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl8_17
    | ~ spl8_25
    | spl8_45
    | ~ spl8_10
    | ~ spl8_4
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f306,f226,f89,f113,f311,f177,f141])).

fof(f226,plain,
    ( spl8_32
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_4
    | ~ spl8_32 ),
    inference(resolution,[],[f227,f90])).

fof(f90,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f226])).

fof(f272,plain,
    ( ~ spl8_4
    | spl8_36 ),
    inference(avatar_split_clause,[],[f263,f246,f89])).

fof(f246,plain,
    ( spl8_36
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f263,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | spl8_36 ),
    inference(resolution,[],[f247,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f247,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f246])).

fof(f258,plain,
    ( spl8_38
    | ~ spl8_31
    | spl8_33 ),
    inference(avatar_split_clause,[],[f254,f229,f223,f256])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(sK5,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | spl8_33 ),
    inference(resolution,[],[f230,f71])).

fof(f71,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f230,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | spl8_33 ),
    inference(avatar_component_clause,[],[f229])).

fof(f248,plain,
    ( ~ spl8_36
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f243,f235,f113,f246])).

fof(f235,plain,
    ( spl8_34
  <=> ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_10
    | ~ spl8_34 ),
    inference(resolution,[],[f236,f114])).

fof(f114,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,
    ( ~ spl8_29
    | spl8_34
    | spl8_31 ),
    inference(avatar_split_clause,[],[f232,f223,f235,f203])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | spl8_31 ),
    inference(resolution,[],[f224,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f224,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f223])).

fof(f231,plain,
    ( ~ spl8_31
    | spl8_32
    | ~ spl8_33
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f221,f206,f93,f229,f226,f223])).

fof(f206,plain,
    ( spl8_30
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(sK6,X2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK5,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(resolution,[],[f207,f94])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f220,plain,
    ( ~ spl8_18
    | ~ spl8_14
    | spl8_29 ),
    inference(avatar_split_clause,[],[f217,f203,f129,f145])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_14
    | spl8_29 ),
    inference(resolution,[],[f216,f130])).

fof(f130,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_29 ),
    inference(resolution,[],[f204,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f204,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f203])).

fof(f215,plain,
    ( ~ spl8_19
    | ~ spl8_18
    | ~ spl8_14
    | spl8_28 ),
    inference(avatar_split_clause,[],[f210,f200,f129,f145,f149])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_14
    | spl8_28 ),
    inference(resolution,[],[f209,f130])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_28 ),
    inference(resolution,[],[f201,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f201,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f200])).

fof(f208,plain,
    ( spl8_15
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_8
    | spl8_30
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f198,f194,f206,f105,f203,f200,f133])).

fof(f194,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ m1_connsp_2(X2,sK3,sK6)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | v2_struct_0(X1)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ r2_hidden(sK6,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6)
        | v2_struct_0(X1)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ r2_hidden(sK6,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl8_27 ),
    inference(resolution,[],[f195,f64])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X2,sK3,sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | v2_struct_0(X0)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( ~ spl8_8
    | spl8_27
    | spl8_1
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f191,f188,f75,f194,f105])).

fof(f188,plain,
    ( spl8_26
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X3)
        | r1_tmap_1(sK3,sK0,sK4,X1)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_connsp_2(X2,sK3,sK6)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1)) )
    | spl8_1
    | ~ spl8_26 ),
    inference(resolution,[],[f189,f76])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f189,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tmap_1(sK3,sK0,sK4,X1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_connsp_2(X0,sK3,X1)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_15
    | ~ spl8_11
    | spl8_26
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f181,f125,f121,f188,f117,f133,f157,f161,f165])).

fof(f181,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1)
        | r1_tmap_1(sK3,sK0,sK4,X1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f180,f122])).

fof(f122,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f180,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_connsp_2(X5,X3,X4)
        | ~ r1_tarski(X5,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_13 ),
    inference(resolution,[],[f168,f126])).

fof(f126,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f168,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f72,f68])).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f179,plain,
    ( spl8_25
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f175,f101,f85,f177])).

fof(f101,plain,
    ( spl8_7
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f175,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f102,f86])).

fof(f102,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f174,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f170,f85,f78,f172])).

fof(f170,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f82,f86])).

fof(f82,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f167,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f38,f165])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f34,f33,f32,f31,f30,f29,f28,f27])).

% (26402)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (26386)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (26398)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (26387)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (26407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (26397)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
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
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK0,X4,X6) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,sK1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK0,X4,X6) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(X2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,sK1)
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK0,X4,X6) )
                          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,sK1)
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK0,X4,X6) )
                        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK1)
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,sK1)
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK0,X4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,sK1)
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK0,sK4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,sK1)
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK0,sK4,X6) )
                & X6 = X7
                & r1_tarski(X5,u1_struct_0(sK2))
                & r2_hidden(X6,X5)
                & v3_pre_topc(X5,sK1)
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK0,sK4,X6) )
              & X6 = X7
              & r1_tarski(sK5,u1_struct_0(sK2))
              & r2_hidden(X6,sK5)
              & v3_pre_topc(sK5,sK1)
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK0,sK4,X6) )
            & X6 = X7
            & r1_tarski(sK5,u1_struct_0(sK2))
            & r2_hidden(X6,sK5)
            & v3_pre_topc(sK5,sK1)
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK0,sK4,sK6) )
          & sK6 = X7
          & r1_tarski(sK5,u1_struct_0(sK2))
          & r2_hidden(sK6,sK5)
          & v3_pre_topc(sK5,sK1)
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK0,sK4,sK6) )
        & sK6 = X7
        & r1_tarski(sK5,u1_struct_0(sK2))
        & r2_hidden(sK6,sK5)
        & v3_pre_topc(sK5,sK1)
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
      & sK6 = sK7
      & r1_tarski(sK5,u1_struct_0(sK2))
      & r2_hidden(sK6,sK5)
      & v3_pre_topc(sK5,sK1)
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f163,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f39,f161])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f159,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f40,f157])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f41,f153])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f151,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f42,f149])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f43,f145])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

% (26390)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f143,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f44,f141])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f135,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f46,f133])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f131,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f47,f129])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f48,f125])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f51,f113])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f55,f97])).

fof(f55,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f56,f93])).

fof(f56,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f57,f89])).

fof(f57,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f58,f85])).

fof(f58,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f59,f78,f75])).

fof(f59,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f60,f78,f75])).

fof(f60,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (26389)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (26399)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (26392)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (26391)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (26405)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (26393)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (26388)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (26392)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f80,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f143,f147,f151,f155,f159,f163,f167,f174,f179,f190,f196,f208,f215,f220,f231,f237,f248,f258,f272,f314,f326,f338,f341,f346,f352,f354])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    ~spl8_4 | ~spl8_31 | ~spl8_33 | ~spl8_5 | ~spl8_49),
% 0.21/0.49    inference(avatar_split_clause,[],[f353,f350,f93,f229,f223,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl8_4 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    spl8_31 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    spl8_33 <=> v3_pre_topc(sK5,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl8_5 <=> r2_hidden(sK6,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    spl8_49 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK6,X0) | ~r1_tarski(X0,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    ~v3_pre_topc(sK5,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(sK5,u1_struct_0(sK2)) | (~spl8_5 | ~spl8_49)),
% 0.21/0.49    inference(resolution,[],[f351,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    r2_hidden(sK6,sK5) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | ~spl8_49),
% 0.21/0.49    inference(avatar_component_clause,[],[f350])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    spl8_15 | ~spl8_28 | ~spl8_29 | ~spl8_8 | spl8_49 | ~spl8_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f348,f330,f350,f105,f203,f200,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl8_15 <=> v2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl8_28 <=> v2_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl8_29 <=> l1_pre_topc(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl8_8 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    spl8_47 <=> ! [X1] : (~m1_connsp_2(X1,sK3,sK6) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X1,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_47),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f347])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_47),
% 0.21/0.49    inference(resolution,[],[f331,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_connsp_2(X1,sK3,sK6) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X1,u1_struct_0(sK2))) ) | ~spl8_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f330])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    ~spl8_14 | ~spl8_9 | ~spl8_18 | ~spl8_6 | ~spl8_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f342,f256,f97,f145,f109,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl8_14 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl8_9 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl8_18 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl8_6 <=> v3_pre_topc(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl8_38 <=> ! [X0] : (~v3_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK3,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | (~spl8_6 | ~spl8_38)),
% 0.21/0.49    inference(resolution,[],[f257,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    v3_pre_topc(sK5,sK1) | ~spl8_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK3,X0)) ) | ~spl8_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f256])).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    spl8_20 | ~spl8_19 | ~spl8_18 | spl8_23 | ~spl8_22 | ~spl8_21 | spl8_17 | spl8_15 | ~spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | ~spl8_8 | ~spl8_25 | spl8_47 | ~spl8_1 | spl8_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f340,f172,f75,f330,f177,f105,f113,f117,f121,f125,f129,f133,f141,f157,f161,f165,f145,f149,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl8_20 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl8_19 <=> v2_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl8_23 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl8_22 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl8_21 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl8_17 <=> v2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl8_13 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl8_12 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl8_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl8_10 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl8_25 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl8_24 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | spl8_24),
% 0.21/0.49    inference(resolution,[],[f337,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ~spl8_24 | spl8_2 | ~spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f336,f85,f78,f172])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl8_3 <=> sK6 = sK7),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | (spl8_2 | ~spl8_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f79,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK6 = sK7 | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ~spl8_19 | spl8_20 | ~spl8_14 | ~spl8_18 | ~spl8_24 | ~spl8_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f321,f311,f172,f145,f129,f153,f149])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    spl8_45 <=> ! [X0] : (~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | (~spl8_24 | ~spl8_45)),
% 0.21/0.49    inference(resolution,[],[f312,f173])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl8_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0)) ) | ~spl8_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f311])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    spl8_17 | ~spl8_25 | spl8_45 | ~spl8_10 | ~spl8_4 | ~spl8_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f306,f226,f89,f113,f311,f177,f141])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl8_32 <=> ! [X1,X0] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | (~spl8_4 | ~spl8_32)),
% 0.21/0.49    inference(resolution,[],[f227,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1)) ) | ~spl8_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f226])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~spl8_4 | spl8_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f263,f246,f89])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    spl8_36 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ~r1_tarski(sK5,u1_struct_0(sK2)) | spl8_36),
% 0.21/0.49    inference(resolution,[],[f247,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | spl8_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f246])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    spl8_38 | ~spl8_31 | spl8_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f254,f229,f223,f256])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(sK5,X0) | ~m1_pre_topc(sK3,X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | spl8_33),
% 0.21/0.49    inference(resolution,[],[f230,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~v3_pre_topc(sK5,sK3) | spl8_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f229])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ~spl8_36 | ~spl8_10 | ~spl8_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f243,f235,f113,f246])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl8_34 <=> ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_10 | ~spl8_34)),
% 0.21/0.49    inference(resolution,[],[f236,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3) | ~spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl8_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~spl8_29 | spl8_34 | spl8_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f232,f223,f235,f203])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | spl8_31),
% 0.21/0.49    inference(resolution,[],[f224,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | spl8_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f223])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~spl8_31 | spl8_32 | ~spl8_33 | ~spl8_5 | ~spl8_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f221,f206,f93,f229,f226,f223])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl8_30 <=> ! [X1,X0,X2] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(sK6,X2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_pre_topc(sK5,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(sK5,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3)) ) | (~spl8_5 | ~spl8_30)),
% 0.21/0.49    inference(resolution,[],[f207,f94])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3)) ) | ~spl8_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~spl8_18 | ~spl8_14 | spl8_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f217,f203,f129,f145])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | (~spl8_14 | spl8_29)),
% 0.21/0.49    inference(resolution,[],[f216,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK1) | ~spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_29),
% 0.21/0.49    inference(resolution,[],[f204,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | spl8_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f203])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~spl8_19 | ~spl8_18 | ~spl8_14 | spl8_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f210,f200,f129,f145,f149])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_14 | spl8_28)),
% 0.21/0.49    inference(resolution,[],[f209,f130])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_28),
% 0.21/0.49    inference(resolution,[],[f201,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v2_pre_topc(sK3) | spl8_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl8_15 | ~spl8_28 | ~spl8_29 | ~spl8_8 | spl8_30 | ~spl8_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f198,f194,f206,f105,f203,f200,f133])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl8_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_27),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK6) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_27),
% 0.21/0.49    inference(resolution,[],[f195,f64])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,sK3,sK6) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | v2_struct_0(X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~spl8_8 | spl8_27 | spl8_1 | ~spl8_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f191,f188,f75,f194,f105])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl8_26 <=> ! [X1,X3,X0,X2] : (~m1_connsp_2(X0,sK3,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | r1_tmap_1(sK3,sK0,sK4,X1) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1))) ) | (spl8_1 | ~spl8_26)),
% 0.21/0.49    inference(resolution,[],[f189,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,sK4,sK6) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r1_tmap_1(sK3,sK0,sK4,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | ~m1_connsp_2(X0,sK3,X1) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2))) ) | ~spl8_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f188])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_15 | ~spl8_11 | spl8_26 | ~spl8_12 | ~spl8_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f181,f125,f121,f188,f117,f133,f157,f161,f165])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X3,sK0,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK0,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | (~spl8_12 | ~spl8_13)),
% 0.21/0.49    inference(resolution,[],[f180,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl8_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_connsp_2(X5,X3,X4) | ~r1_tarski(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_13),
% 0.21/0.49    inference(resolution,[],[f168,f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl8_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f68])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl8_25 | ~spl8_3 | ~spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f175,f101,f85,f177])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl8_7 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_7)),
% 0.21/0.49    inference(superposition,[],[f102,f86])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl8_24 | ~spl8_2 | ~spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f85,f78,f172])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | (~spl8_2 | ~spl8_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f82,f86])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~spl8_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f165])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f34,f33,f32,f31,f30,f29,f28,f27])).
% 0.21/0.49  % (26402)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (26386)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (26398)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (26387)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (26397)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl8_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f161])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl8_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f157])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ~spl8_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f153])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl8_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f149])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl8_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f145])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % (26390)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~spl8_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f141])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~spl8_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f133])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl8_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f129])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f125])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl8_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f121])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f117])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f113])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl8_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f109])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f105])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f101])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f97])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v3_pre_topc(sK5,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f93])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r2_hidden(sK6,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f89])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f85])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    sK6 = sK7),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl8_1 | spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f78,f75])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl8_1 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f78,f75])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26392)------------------------------
% 0.21/0.50  % (26392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26392)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26392)Memory used [KB]: 11001
% 0.21/0.50  % (26392)Time elapsed: 0.068 s
% 0.21/0.50  % (26392)------------------------------
% 0.21/0.50  % (26392)------------------------------
% 0.21/0.50  % (26401)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (26383)Success in time 0.14 s
%------------------------------------------------------------------------------
