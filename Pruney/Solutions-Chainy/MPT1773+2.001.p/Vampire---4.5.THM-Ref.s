%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 349 expanded)
%              Number of leaves         :   43 ( 149 expanded)
%              Depth                    :    8
%              Number of atoms          :  736 (3020 expanded)
%              Number of equality atoms :   14 ( 113 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f187,f200,f205,f215,f229,f231,f251,f252,f257,f267,f273,f287,f308,f314,f319,f325,f330])).

fof(f330,plain,
    ( ~ spl11_17
    | ~ spl11_19
    | ~ spl11_39
    | spl11_40 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl11_17
    | ~ spl11_19
    | ~ spl11_39
    | spl11_40 ),
    inference(unit_resulting_resolution,[],[f170,f312,f186,f324,f85])).

fof(f85,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | sP10(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_connsp_2(X5,X3,X7) )
    <=> ~ sP10(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f324,plain,
    ( ~ sP10(sK3,sK2,sK6)
    | spl11_40 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl11_40
  <=> sP10(sK3,sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f186,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl11_19
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f312,plain,
    ( m1_connsp_2(sK5,sK3,sK6)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl11_39
  <=> m1_connsp_2(sK5,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f170,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl11_17
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f325,plain,
    ( ~ spl11_40
    | spl11_29
    | spl11_7
    | ~ spl11_23
    | ~ spl11_18
    | ~ spl11_13
    | ~ spl11_26
    | ~ spl11_22
    | ~ spl11_1
    | ~ spl11_14
    | spl11_2
    | ~ spl11_15
    | spl11_3
    | ~ spl11_6
    | ~ spl11_5
    | spl11_4
    | ~ spl11_9
    | ~ spl11_8
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f320,f248,f123,f128,f103,f108,f113,f98,f158,f93,f153,f88,f202,f226,f148,f173,f212,f118,f244,f322])).

fof(f244,plain,
    ( spl11_29
  <=> r1_tmap_1(sK3,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f118,plain,
    ( spl11_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f212,plain,
    ( spl11_23
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f173,plain,
    ( spl11_18
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f148,plain,
    ( spl11_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f226,plain,
    ( spl11_26
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f202,plain,
    ( spl11_22
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f88,plain,
    ( spl11_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f153,plain,
    ( spl11_14
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f93,plain,
    ( spl11_2
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f158,plain,
    ( spl11_15
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f98,plain,
    ( spl11_3
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f113,plain,
    ( spl11_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f108,plain,
    ( spl11_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f103,plain,
    ( spl11_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f128,plain,
    ( spl11_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f123,plain,
    ( spl11_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f248,plain,
    ( spl11_30
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f320,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ sP10(sK3,sK2,sK6)
    | ~ spl11_30 ),
    inference(resolution,[],[f250,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | v2_struct_0(X0)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ sP10(X3,X2,X7) ) ),
    inference(general_splitting,[],[f79,f85_D])).

fof(f79,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f250,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f319,plain,
    ( ~ spl11_11
    | ~ spl11_18
    | ~ spl11_33
    | ~ spl11_36
    | spl11_39 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_18
    | ~ spl11_33
    | ~ spl11_36
    | spl11_39 ),
    inference(unit_resulting_resolution,[],[f140,f266,f175,f313,f289])).

fof(f289,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k1_tops_1(sK3,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(X1,X2)
        | m1_connsp_2(sK5,sK3,X1) )
    | ~ spl11_36 ),
    inference(resolution,[],[f286,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK3,sK5))
        | m1_connsp_2(sK5,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl11_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | m1_connsp_2(sK5,sK3,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK3,sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f313,plain,
    ( ~ m1_connsp_2(sK5,sK3,sK6)
    | spl11_39 ),
    inference(avatar_component_clause,[],[f311])).

fof(f175,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f266,plain,
    ( r1_tarski(sK5,k1_tops_1(sK3,sK5))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl11_33
  <=> r1_tarski(sK5,k1_tops_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f140,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_11
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f314,plain,
    ( ~ spl11_17
    | ~ spl11_39
    | ~ spl11_19
    | spl11_38 ),
    inference(avatar_split_clause,[],[f309,f305,f184,f311,f168])).

fof(f305,plain,
    ( spl11_38
  <=> sP9(sK3,sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f309,plain,
    ( ~ m1_connsp_2(sK5,sK3,sK6)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl11_19
    | spl11_38 ),
    inference(resolution,[],[f307,f209])).

fof(f209,plain,
    ( ! [X4,X3] :
        ( sP9(sK3,X3,X4)
        | ~ m1_connsp_2(sK5,sK3,X4)
        | ~ r1_tarski(sK5,u1_struct_0(X3)) )
    | ~ spl11_19 ),
    inference(resolution,[],[f186,f83])).

fof(f83,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | sP9(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f83_D])).

fof(f83_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_connsp_2(X5,X3,X7) )
    <=> ~ sP9(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f307,plain,
    ( ~ sP9(sK3,sK2,sK6)
    | spl11_38 ),
    inference(avatar_component_clause,[],[f305])).

fof(f308,plain,
    ( ~ spl11_38
    | ~ spl11_29
    | spl11_7
    | ~ spl11_23
    | ~ spl11_18
    | ~ spl11_13
    | ~ spl11_26
    | ~ spl11_22
    | ~ spl11_1
    | ~ spl11_14
    | spl11_2
    | ~ spl11_15
    | spl11_3
    | ~ spl11_6
    | ~ spl11_5
    | spl11_4
    | ~ spl11_9
    | ~ spl11_8
    | spl11_30 ),
    inference(avatar_split_clause,[],[f253,f248,f123,f128,f103,f108,f113,f98,f158,f93,f153,f88,f202,f226,f148,f173,f212,f118,f244,f305])).

fof(f253,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ sP9(sK3,sK2,sK6)
    | spl11_30 ),
    inference(resolution,[],[f249,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | v2_struct_0(X0)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ sP9(X3,X2,X7) ) ),
    inference(general_splitting,[],[f78,f83_D])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X6)
      | X6 != X7
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f249,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl11_30 ),
    inference(avatar_component_clause,[],[f248])).

fof(f287,plain,
    ( spl11_2
    | spl11_36
    | ~ spl11_21
    | ~ spl11_25
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f206,f184,f221,f195,f285,f93])).

fof(f195,plain,
    ( spl11_21
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f221,plain,
    ( spl11_25
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v2_struct_0(sK3)
        | ~ r2_hidden(X0,k1_tops_1(sK3,sK5))
        | m1_connsp_2(sK5,sK3,X0) )
    | ~ spl11_19 ),
    inference(resolution,[],[f186,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f273,plain,(
    spl11_32 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl11_32 ),
    inference(unit_resulting_resolution,[],[f82,f262])).

fof(f262,plain,
    ( ~ r1_tarski(sK5,sK5)
    | spl11_32 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl11_32
  <=> r1_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f267,plain,
    ( ~ spl11_10
    | ~ spl11_32
    | spl11_33
    | ~ spl11_19
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f258,f255,f184,f264,f260,f133])).

fof(f133,plain,
    ( spl11_10
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f255,plain,
    ( spl11_31
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | r1_tarski(X2,k1_tops_1(sK3,sK5))
        | ~ r1_tarski(X2,sK5)
        | ~ v3_pre_topc(X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f258,plain,
    ( r1_tarski(sK5,k1_tops_1(sK3,sK5))
    | ~ r1_tarski(sK5,sK5)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ spl11_19
    | ~ spl11_31 ),
    inference(resolution,[],[f256,f186])).

fof(f256,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | r1_tarski(X2,k1_tops_1(sK3,sK5))
        | ~ r1_tarski(X2,sK5)
        | ~ v3_pre_topc(X2,sK3) )
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( ~ spl11_21
    | spl11_31
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f208,f184,f255,f195])).

fof(f208,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v3_pre_topc(X2,sK3)
        | ~ r1_tarski(X2,sK5)
        | r1_tarski(X2,k1_tops_1(sK3,sK5)) )
    | ~ spl11_19 ),
    inference(resolution,[],[f186,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f252,plain,
    ( ~ spl11_29
    | ~ spl11_30
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f242,f143,f248,f244])).

fof(f143,plain,
    ( spl11_12
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f242,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f38,f145])).

fof(f145,plain,
    ( sK6 = sK7
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f38,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X3)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
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
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X3) )
                                       => ( r1_tmap_1(X3,X1,X4,X6)
                                        <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f251,plain,
    ( spl11_29
    | spl11_30
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f241,f143,f248,f244])).

fof(f241,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ spl11_12 ),
    inference(forward_demodulation,[],[f37,f145])).

fof(f37,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f16])).

fof(f231,plain,
    ( ~ spl11_8
    | ~ spl11_9
    | ~ spl11_14
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_14
    | spl11_25 ),
    inference(unit_resulting_resolution,[],[f130,f125,f155,f223,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f223,plain,
    ( ~ v2_pre_topc(sK3)
    | spl11_25 ),
    inference(avatar_component_clause,[],[f221])).

fof(f155,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f125,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f229,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f48,f226])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f215,plain,
    ( spl11_23
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f188,f163,f143,f212])).

fof(f163,plain,
    ( spl11_16
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f188,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f165,f145])).

fof(f165,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f205,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f47,f202])).

fof(f47,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f200,plain,
    ( ~ spl11_9
    | ~ spl11_14
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_14
    | spl11_21 ),
    inference(unit_resulting_resolution,[],[f130,f155,f197,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f197,plain,
    ( ~ l1_pre_topc(sK3)
    | spl11_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f187,plain,(
    spl11_19 ),
    inference(avatar_split_clause,[],[f45,f184])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f44,f173])).

fof(f44,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f42,f168])).

fof(f42,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f166,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f39,f163])).

fof(f39,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,(
    spl11_15 ),
    inference(avatar_split_clause,[],[f53,f158])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f51,f153])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f151,plain,(
    spl11_13 ),
    inference(avatar_split_clause,[],[f49,f148])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f146,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f43,f143])).

fof(f43,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f41,f138])).

fof(f41,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f40,f133])).

fof(f40,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f59,f128])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    ~ spl11_4 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (29955)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (29940)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (29955)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f187,f200,f205,f215,f229,f231,f251,f252,f257,f267,f273,f287,f308,f314,f319,f325,f330])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    ~spl11_17 | ~spl11_19 | ~spl11_39 | spl11_40),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f327])).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    $false | (~spl11_17 | ~spl11_19 | ~spl11_39 | spl11_40)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f170,f312,f186,f324,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X2,X7,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | sP10(X3,X2,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f85_D])).
% 0.22/0.53  fof(f85_D,plain,(
% 0.22/0.53    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7)) ) <=> ~sP10(X3,X2,X7)) )),
% 0.22/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    ~sP10(sK3,sK2,sK6) | spl11_40),
% 0.22/0.53    inference(avatar_component_clause,[],[f322])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    spl11_40 <=> sP10(sK3,sK2,sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~spl11_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl11_19 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    m1_connsp_2(sK5,sK3,sK6) | ~spl11_39),
% 0.22/0.53    inference(avatar_component_clause,[],[f311])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl11_39 <=> m1_connsp_2(sK5,sK3,sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl11_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    spl11_17 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    ~spl11_40 | spl11_29 | spl11_7 | ~spl11_23 | ~spl11_18 | ~spl11_13 | ~spl11_26 | ~spl11_22 | ~spl11_1 | ~spl11_14 | spl11_2 | ~spl11_15 | spl11_3 | ~spl11_6 | ~spl11_5 | spl11_4 | ~spl11_9 | ~spl11_8 | ~spl11_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f320,f248,f123,f128,f103,f108,f113,f98,f158,f93,f153,f88,f202,f226,f148,f173,f212,f118,f244,f322])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    spl11_29 <=> r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl11_7 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    spl11_23 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    spl11_18 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl11_13 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl11_26 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl11_22 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    spl11_1 <=> v1_funct_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    spl11_14 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl11_2 <=> v2_struct_0(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    spl11_15 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl11_3 <=> v2_struct_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl11_6 <=> l1_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl11_5 <=> v2_pre_topc(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl11_4 <=> v2_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl11_9 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl11_8 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    spl11_30 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 0.22/0.53  fof(f320,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | r1_tmap_1(sK3,sK1,sK4,sK6) | ~sP10(sK3,sK2,sK6) | ~spl11_30),
% 0.22/0.53    inference(resolution,[],[f250,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | r1_tmap_1(X3,X1,X4,X7) | ~sP10(X3,X2,X7)) )),
% 0.22/0.53    inference(general_splitting,[],[f79,f85_D])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.22/0.53    inference(equality_resolution,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl11_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f248])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    ~spl11_11 | ~spl11_18 | ~spl11_33 | ~spl11_36 | spl11_39),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f316])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    $false | (~spl11_11 | ~spl11_18 | ~spl11_33 | ~spl11_36 | spl11_39)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f140,f266,f175,f313,f289])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r1_tarski(X2,k1_tops_1(sK3,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X2) | m1_connsp_2(sK5,sK3,X1)) ) | ~spl11_36),
% 0.22/0.53    inference(resolution,[],[f286,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK3,sK5)) | m1_connsp_2(sK5,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl11_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f285])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    spl11_36 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK5,sK3,X0) | ~r2_hidden(X0,k1_tops_1(sK3,sK5)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    ~m1_connsp_2(sK5,sK3,sK6) | spl11_39),
% 0.22/0.53    inference(avatar_component_clause,[],[f311])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl11_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f173])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    r1_tarski(sK5,k1_tops_1(sK3,sK5)) | ~spl11_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f264])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl11_33 <=> r1_tarski(sK5,k1_tops_1(sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    r2_hidden(sK6,sK5) | ~spl11_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    spl11_11 <=> r2_hidden(sK6,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    ~spl11_17 | ~spl11_39 | ~spl11_19 | spl11_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f309,f305,f184,f311,f168])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    spl11_38 <=> sP9(sK3,sK2,sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    ~m1_connsp_2(sK5,sK3,sK6) | ~r1_tarski(sK5,u1_struct_0(sK2)) | (~spl11_19 | spl11_38)),
% 0.22/0.53    inference(resolution,[],[f307,f209])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ( ! [X4,X3] : (sP9(sK3,X3,X4) | ~m1_connsp_2(sK5,sK3,X4) | ~r1_tarski(sK5,u1_struct_0(X3))) ) | ~spl11_19),
% 0.22/0.53    inference(resolution,[],[f186,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X7,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | sP9(X3,X2,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f83_D])).
% 0.22/0.53  fof(f83_D,plain,(
% 0.22/0.53    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7)) ) <=> ~sP9(X3,X2,X7)) )),
% 0.22/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.22/0.53  fof(f307,plain,(
% 0.22/0.53    ~sP9(sK3,sK2,sK6) | spl11_38),
% 0.22/0.53    inference(avatar_component_clause,[],[f305])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    ~spl11_38 | ~spl11_29 | spl11_7 | ~spl11_23 | ~spl11_18 | ~spl11_13 | ~spl11_26 | ~spl11_22 | ~spl11_1 | ~spl11_14 | spl11_2 | ~spl11_15 | spl11_3 | ~spl11_6 | ~spl11_5 | spl11_4 | ~spl11_9 | ~spl11_8 | spl11_30),
% 0.22/0.53    inference(avatar_split_clause,[],[f253,f248,f123,f128,f103,f108,f113,f98,f158,f93,f153,f88,f202,f226,f148,f173,f212,f118,f244,f305])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | ~sP9(sK3,sK2,sK6) | spl11_30),
% 0.22/0.53    inference(resolution,[],[f249,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | v2_struct_0(X0) | ~r1_tmap_1(X3,X1,X4,X7) | ~sP9(X3,X2,X7)) )),
% 0.22/0.53    inference(general_splitting,[],[f78,f83_D])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7)) )),
% 0.22/0.53    inference(equality_resolution,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X6) | X6 != X7 | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | spl11_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f248])).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    spl11_2 | spl11_36 | ~spl11_21 | ~spl11_25 | ~spl11_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f206,f184,f221,f195,f285,f93])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl11_21 <=> l1_pre_topc(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    spl11_25 <=> v2_pre_topc(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~r2_hidden(X0,k1_tops_1(sK3,sK5)) | m1_connsp_2(sK5,sK3,X0)) ) | ~spl11_19),
% 0.22/0.53    inference(resolution,[],[f186,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    spl11_32),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f268])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    $false | spl11_32),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f82,f262])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    ~r1_tarski(sK5,sK5) | spl11_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f260])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    spl11_32 <=> r1_tarski(sK5,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    ~spl11_10 | ~spl11_32 | spl11_33 | ~spl11_19 | ~spl11_31),
% 0.22/0.54    inference(avatar_split_clause,[],[f258,f255,f184,f264,f260,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    spl11_10 <=> v3_pre_topc(sK5,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    spl11_31 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | r1_tarski(X2,k1_tops_1(sK3,sK5)) | ~r1_tarski(X2,sK5) | ~v3_pre_topc(X2,sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    r1_tarski(sK5,k1_tops_1(sK3,sK5)) | ~r1_tarski(sK5,sK5) | ~v3_pre_topc(sK5,sK3) | (~spl11_19 | ~spl11_31)),
% 0.22/0.54    inference(resolution,[],[f256,f186])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | r1_tarski(X2,k1_tops_1(sK3,sK5)) | ~r1_tarski(X2,sK5) | ~v3_pre_topc(X2,sK3)) ) | ~spl11_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f255])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    ~spl11_21 | spl11_31 | ~spl11_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f208,f184,f255,f195])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v3_pre_topc(X2,sK3) | ~r1_tarski(X2,sK5) | r1_tarski(X2,k1_tops_1(sK3,sK5))) ) | ~spl11_19),
% 0.22/0.54    inference(resolution,[],[f186,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    ~spl11_29 | ~spl11_30 | ~spl11_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f242,f143,f248,f244])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    spl11_12 <=> sK6 = sK7),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK6) | ~spl11_12),
% 0.22/0.54    inference(forward_demodulation,[],[f38,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    sK6 = sK7 | ~spl11_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f143])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f13])).
% 0.22/0.54  fof(f13,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    spl11_29 | spl11_30 | ~spl11_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f241,f143,f248,f244])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK6) | ~spl11_12),
% 0.22/0.54    inference(forward_demodulation,[],[f37,f145])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ~spl11_8 | ~spl11_9 | ~spl11_14 | spl11_25),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f230])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    $false | (~spl11_8 | ~spl11_9 | ~spl11_14 | spl11_25)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f130,f125,f155,f223,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ~v2_pre_topc(sK3) | spl11_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f221])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK0) | ~spl11_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f153])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl11_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f123])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl11_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl11_26),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f226])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    spl11_23 | ~spl11_12 | ~spl11_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f188,f163,f143,f212])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    spl11_16 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl11_12 | ~spl11_16)),
% 0.22/0.54    inference(forward_demodulation,[],[f165,f145])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl11_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f163])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl11_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f202])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ~spl11_9 | ~spl11_14 | spl11_21),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f199])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    $false | (~spl11_9 | ~spl11_14 | spl11_21)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f130,f155,f197,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ~l1_pre_topc(sK3) | spl11_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f195])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    spl11_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f184])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    spl11_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f173])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    spl11_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f168])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    spl11_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f163])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    spl11_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f158])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    spl11_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f51,f153])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl11_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f148])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl11_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f143])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    sK6 = sK7),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    spl11_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f138])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    r2_hidden(sK6,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl11_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f133])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    v3_pre_topc(sK5,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    spl11_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f59,f128])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    spl11_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f58,f123])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ~spl11_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f57,f118])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl11_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f56,f113])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl11_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f108])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    v2_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ~spl11_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f103])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ~spl11_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f98])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ~v2_struct_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ~spl11_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f50,f93])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ~v2_struct_0(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl11_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f88])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (29955)------------------------------
% 0.22/0.54  % (29955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29955)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (29955)Memory used [KB]: 11129
% 0.22/0.54  % (29955)Time elapsed: 0.108 s
% 0.22/0.54  % (29955)------------------------------
% 0.22/0.54  % (29955)------------------------------
% 0.22/0.54  % (29948)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (29932)Success in time 0.173 s
%------------------------------------------------------------------------------
