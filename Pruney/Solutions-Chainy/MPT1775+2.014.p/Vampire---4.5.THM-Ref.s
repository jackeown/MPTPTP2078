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
% DateTime   : Thu Dec  3 13:18:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 668 expanded)
%              Number of leaves         :   60 ( 344 expanded)
%              Depth                    :   18
%              Number of atoms          : 1586 (8606 expanded)
%              Number of equality atoms :   40 ( 450 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180,f184,f197,f202,f215,f221,f254,f262,f265,f274,f280,f288,f294,f301,f316,f319,f324,f329,f331,f347,f359,f360])).

fof(f360,plain,
    ( sK5 != sK6
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f359,plain,
    ( spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | spl8_12
    | ~ spl8_11
    | spl8_14
    | ~ spl8_13
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_6
    | ~ spl8_1
    | spl8_21 ),
    inference(avatar_split_clause,[],[f350,f195,f104,f126,f200,f122,f134,f138,f142,f154,f158,f146,f150,f162,f166,f170,f174,f178,f182])).

fof(f182,plain,
    ( spl8_20
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f178,plain,
    ( spl8_19
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f174,plain,
    ( spl8_18
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f170,plain,
    ( spl8_17
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f166,plain,
    ( spl8_16
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f162,plain,
    ( spl8_15
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f150,plain,
    ( spl8_12
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f146,plain,
    ( spl8_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f158,plain,
    ( spl8_14
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f154,plain,
    ( spl8_13
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f142,plain,
    ( spl8_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f138,plain,
    ( spl8_9
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f134,plain,
    ( spl8_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f122,plain,
    ( spl8_5
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f200,plain,
    ( spl8_22
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f126,plain,
    ( spl8_6
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f104,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f195,plain,
    ( spl8_21
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f350,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_21 ),
    inference(resolution,[],[f345,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f345,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f195])).

% (15485)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f347,plain,
    ( ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | spl8_20
    | ~ spl8_11
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f342,f252,f146,f182,f195,f178,f174])).

fof(f252,plain,
    ( spl8_30
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f342,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_11
    | ~ spl8_30 ),
    inference(resolution,[],[f253,f147])).

fof(f147,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f331,plain,
    ( ~ spl8_25
    | spl8_41 ),
    inference(avatar_split_clause,[],[f330,f327,f234])).

fof(f234,plain,
    ( spl8_25
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f327,plain,
    ( spl8_41
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f330,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_41 ),
    inference(resolution,[],[f328,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f328,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_41 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( spl8_14
    | ~ spl8_41
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f325,f322,f327,f158])).

fof(f322,plain,
    ( spl8_40
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f325,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_40 ),
    inference(resolution,[],[f323,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f323,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f322])).

fof(f324,plain,
    ( ~ spl8_22
    | spl8_40
    | spl8_39 ),
    inference(avatar_split_clause,[],[f320,f314,f322,f200])).

fof(f314,plain,
    ( spl8_39
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f320,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | spl8_39 ),
    inference(resolution,[],[f315,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f315,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | spl8_39 ),
    inference(avatar_component_clause,[],[f314])).

fof(f319,plain,
    ( ~ spl8_27
    | ~ spl8_28
    | ~ spl8_26
    | ~ spl8_7
    | ~ spl8_6
    | spl8_38 ),
    inference(avatar_split_clause,[],[f317,f311,f126,f130,f237,f244,f241])).

fof(f241,plain,
    ( spl8_27
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f244,plain,
    ( spl8_28
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f237,plain,
    ( spl8_26
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f130,plain,
    ( spl8_7
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f311,plain,
    ( spl8_38
  <=> v3_pre_topc(u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f317,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl8_38 ),
    inference(resolution,[],[f312,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f36])).

% (15490)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f312,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | spl8_38 ),
    inference(avatar_component_clause,[],[f311])).

fof(f316,plain,
    ( spl8_12
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_26
    | ~ spl8_5
    | ~ spl8_38
    | ~ spl8_39
    | spl8_34 ),
    inference(avatar_split_clause,[],[f309,f292,f314,f311,f122,f237,f244,f241,f150])).

fof(f292,plain,
    ( spl8_34
  <=> m1_connsp_2(u1_struct_0(sK2),sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f309,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_34 ),
    inference(resolution,[],[f293,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f293,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK2),sK3,sK5)
    | spl8_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f301,plain,
    ( spl8_12
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_5
    | ~ spl8_34
    | spl8_33 ),
    inference(avatar_split_clause,[],[f299,f286,f292,f122,f244,f241,f150])).

fof(f286,plain,
    ( spl8_33
  <=> m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f299,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK2),sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_33 ),
    inference(resolution,[],[f287,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK7(X0,X1,X2),X2)
                & v3_pre_topc(sK7(X0,X1,X2),X0)
                & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
                & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK7(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK7(X0,X1,X2),X2)
        & v3_pre_topc(sK7(X0,X1,X2),X0)
        & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

% (15501)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f287,plain,
    ( ~ m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5)
    | spl8_33 ),
    inference(avatar_component_clause,[],[f286])).

fof(f294,plain,
    ( spl8_12
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_5
    | ~ spl8_34
    | spl8_32 ),
    inference(avatar_split_clause,[],[f289,f283,f292,f122,f244,f241,f150])).

fof(f283,plain,
    ( spl8_32
  <=> m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f289,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK2),sK3,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_32 ),
    inference(resolution,[],[f284,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f95])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f284,plain,
    ( ~ m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f283])).

fof(f288,plain,
    ( ~ spl8_32
    | ~ spl8_33
    | ~ spl8_22
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f281,f247,f122,f200,f286,f283])).

fof(f247,plain,
    ( spl8_29
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5)
        | ~ m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f281,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5)
    | ~ m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(resolution,[],[f248,f123])).

fof(f123,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5)
        | ~ m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f280,plain,
    ( ~ spl8_19
    | ~ spl8_18
    | ~ spl8_11
    | spl8_27 ),
    inference(avatar_split_clause,[],[f276,f241,f146,f174,f178])).

fof(f276,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_11
    | spl8_27 ),
    inference(resolution,[],[f275,f147])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_27 ),
    inference(resolution,[],[f242,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f242,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f241])).

fof(f274,plain,
    ( ~ spl8_18
    | ~ spl8_11
    | spl8_28 ),
    inference(avatar_split_clause,[],[f271,f244,f146,f174])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_11
    | spl8_28 ),
    inference(resolution,[],[f270,f147])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_28 ),
    inference(resolution,[],[f245,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f245,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f265,plain,
    ( ~ spl8_28
    | ~ spl8_6
    | spl8_26 ),
    inference(avatar_split_clause,[],[f263,f237,f126,f244])).

fof(f263,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | spl8_26 ),
    inference(resolution,[],[f238,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f238,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f237])).

fof(f262,plain,
    ( ~ spl8_18
    | ~ spl8_13
    | spl8_25 ),
    inference(avatar_split_clause,[],[f257,f234,f154,f174])).

fof(f257,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_13
    | spl8_25 ),
    inference(resolution,[],[f255,f155])).

fof(f155,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_25 ),
    inference(resolution,[],[f235,f77])).

fof(f235,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f234])).

fof(f254,plain,
    ( ~ spl8_25
    | ~ spl8_26
    | ~ spl8_6
    | spl8_12
    | ~ spl8_27
    | ~ spl8_28
    | spl8_29
    | ~ spl8_22
    | spl8_14
    | spl8_30
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f232,f219,f130,f252,f158,f200,f247,f244,f241,f150,f126,f237,f234])).

fof(f219,plain,
    ( spl8_24
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(resolution,[],[f230,f131])).

fof(f131,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f230,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),sK5)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(sK7(X0,X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(sK7(X0,X1,u1_struct_0(X2)),sK3,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f229,f76])).

fof(f229,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_struct_0(X3)
        | ~ m1_subset_1(sK7(X1,X2,u1_struct_0(X3)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X3,sK1,k3_tmap_1(X0,sK1,sK3,X3,sK4),sK5)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X3,X1)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_connsp_2(sK7(X1,X2,u1_struct_0(X3)),sK3,sK5)
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | v2_struct_0(X0) )
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK7(X1,X2,u1_struct_0(X3)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X3,sK1,k3_tmap_1(X0,sK1,sK3,X3,sK4),sK5)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X3,X1)
        | ~ v1_tsep_1(X3,X1)
        | ~ m1_connsp_2(sK7(X1,X2,u1_struct_0(X3)),sK3,sK5)
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ l1_struct_0(X3)
        | v2_struct_0(X3) )
    | ~ spl8_24 ),
    inference(resolution,[],[f227,f79])).

fof(f227,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(u1_struct_0(X2))
        | v2_struct_0(X3)
        | ~ m1_subset_1(sK7(X0,X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),sK5)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_connsp_2(sK7(X0,X1,u1_struct_0(X2)),sK3,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(X2)) )
    | ~ spl8_24 ),
    inference(resolution,[],[f226,f94])).

fof(f226,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,u1_struct_0(X0))
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_tsep_1(X0,X2) )
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ r2_hidden(X3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f224,f102])).

fof(f224,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v3_pre_topc(u1_struct_0(X0),X2)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ r2_hidden(X3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ r2_hidden(X3,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),X2)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f222,f85])).

fof(f222,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_connsp_2(u1_struct_0(X0),X2,X3)
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f220,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK7(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f84,f95])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK7(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_connsp_2(X2,sK3,sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( ~ spl8_5
    | spl8_24
    | spl8_1
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f216,f213,f104,f219,f122])).

fof(f213,plain,
    ( spl8_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X3)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_connsp_2(X2,sK3,sK5)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1)) )
    | spl8_1
    | ~ spl8_23 ),
    inference(resolution,[],[f214,f105])).

fof(f105,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f214,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tmap_1(sK3,sK1,sK4,X1)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_connsp_2(X0,sK3,X1)
        | ~ r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ r1_tarski(X0,u1_struct_0(X2)) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | spl8_12
    | ~ spl8_8
    | spl8_23
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f206,f142,f138,f213,f134,f150,f162,f166,f170])).

fof(f206,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_connsp_2(X0,sK3,X1)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(resolution,[],[f205,f139])).

fof(f139,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f205,plain,
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
    | ~ spl8_10 ),
    inference(resolution,[],[f185,f143])).

fof(f143,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f185,plain,(
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
    inference(subsumption_resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f202,plain,
    ( spl8_22
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f198,f118,f114,f200])).

fof(f114,plain,
    ( spl8_3
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f118,plain,
    ( spl8_4
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f198,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f119,f115])).

% (15481)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f115,plain,
    ( sK5 = sK6
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f119,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f197,plain,
    ( spl8_21
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f193,f114,f107,f195])).

fof(f107,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f193,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f111,f115])).

fof(f111,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f184,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f56,f182])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK1,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & v1_tsep_1(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f49,f48,f47,f46,f45,f44,f43])).

% (15480)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X1,X4,X5) )
                            & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X1,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK1,X4,X5) )
                          & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK1,X4,X5) )
                        & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & v1_tsep_1(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK1,X4,X5) )
                      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & v1_tsep_1(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK1,X4,X5) )
                    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & v1_tsep_1(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                  & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & v1_tsep_1(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK1,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & v1_tsep_1(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
              & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK1,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & v1_tsep_1(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
            & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK1,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK1,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK1,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK1,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f180,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f57,f178])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f176,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f58,f174])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f172,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f59,f170])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f168,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f60,f166])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f164,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f61,f162])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f160,plain,(
    ~ spl8_14 ),
    inference(avatar_split_clause,[],[f62,f158])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f156,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f63,f154])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f152,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f64,f150])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f148,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f65,f146])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f144,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f66,f142])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f140,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f67,f138])).

fof(f67,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f136,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f68,f134])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f69,f130])).

fof(f69,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f128,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f70,f126])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f124,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f71,f122])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f72,f118])).

fof(f72,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f73,f114])).

fof(f73,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f74,f107,f104])).

fof(f74,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f109,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f75,f107,f104])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (15497)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (15496)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (15483)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (15488)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (15487)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f109,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f176,f180,f184,f197,f202,f215,f221,f254,f262,f265,f274,f280,f288,f294,f301,f316,f319,f324,f329,f331,f347,f359,f360])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    sK5 != sK6 | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    spl8_20 | ~spl8_19 | ~spl8_18 | spl8_17 | ~spl8_16 | ~spl8_15 | spl8_12 | ~spl8_11 | spl8_14 | ~spl8_13 | ~spl8_10 | ~spl8_9 | ~spl8_8 | ~spl8_5 | ~spl8_22 | ~spl8_6 | ~spl8_1 | spl8_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f350,f195,f104,f126,f200,f122,f134,f138,f142,f154,f158,f146,f150,f162,f166,f170,f174,f178,f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl8_20 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl8_19 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl8_18 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl8_17 <=> v2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl8_16 <=> v2_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    spl8_15 <=> l1_pre_topc(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl8_12 <=> v2_struct_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl8_11 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl8_14 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl8_13 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl8_10 <=> v1_funct_1(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl8_9 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl8_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl8_5 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    spl8_22 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl8_6 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl8_1 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl8_21 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_21),
% 0.21/0.48    inference(resolution,[],[f345,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl8_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  % (15485)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    ~spl8_18 | ~spl8_19 | ~spl8_21 | spl8_20 | ~spl8_11 | ~spl8_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f342,f252,f146,f182,f195,f178,f174])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    spl8_30 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl8_11 | ~spl8_30)),
% 0.21/0.48    inference(resolution,[],[f253,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK0) | ~spl8_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl8_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f252])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    ~spl8_25 | spl8_41),
% 0.21/0.48    inference(avatar_split_clause,[],[f330,f327,f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    spl8_25 <=> l1_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    spl8_41 <=> l1_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | spl8_41),
% 0.21/0.48    inference(resolution,[],[f328,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    ~l1_struct_0(sK2) | spl8_41),
% 0.21/0.48    inference(avatar_component_clause,[],[f327])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    spl8_14 | ~spl8_41 | ~spl8_40),
% 0.21/0.48    inference(avatar_split_clause,[],[f325,f322,f327,f158])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    spl8_40 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl8_40),
% 0.21/0.48    inference(resolution,[],[f323,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK2)) | ~spl8_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f322])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ~spl8_22 | spl8_40 | spl8_39),
% 0.21/0.48    inference(avatar_split_clause,[],[f320,f314,f322,f200])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    spl8_39 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | spl8_39),
% 0.21/0.48    inference(resolution,[],[f315,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ~r2_hidden(sK5,u1_struct_0(sK2)) | spl8_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f314])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ~spl8_27 | ~spl8_28 | ~spl8_26 | ~spl8_7 | ~spl8_6 | spl8_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f317,f311,f126,f130,f237,f244,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    spl8_27 <=> v2_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl8_28 <=> l1_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl8_26 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl8_7 <=> v1_tsep_1(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    spl8_38 <=> v3_pre_topc(u1_struct_0(sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | spl8_38),
% 0.21/0.48    inference(resolution,[],[f312,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f36])).
% 0.21/0.49  % (15490)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ~v3_pre_topc(u1_struct_0(sK2),sK3) | spl8_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f311])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl8_12 | ~spl8_27 | ~spl8_28 | ~spl8_26 | ~spl8_5 | ~spl8_38 | ~spl8_39 | spl8_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f309,f292,f314,f311,f122,f237,f244,f241,f150])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    spl8_34 <=> m1_connsp_2(u1_struct_0(sK2),sK3,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ~r2_hidden(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_34),
% 0.21/0.49    inference(resolution,[],[f293,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    ~m1_connsp_2(u1_struct_0(sK2),sK3,sK5) | spl8_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f292])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl8_12 | ~spl8_27 | ~spl8_28 | ~spl8_5 | ~spl8_34 | spl8_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f299,f286,f292,f122,f244,f241,f150])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    spl8_33 <=> m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~m1_connsp_2(u1_struct_0(sK2),sK3,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_33),
% 0.21/0.49    inference(resolution,[],[f287,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK7(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(sK7(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK7(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK7(X0,X1,X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (15501)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5) | spl8_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f286])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    spl8_12 | ~spl8_27 | ~spl8_28 | ~spl8_5 | ~spl8_34 | spl8_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f283,f292,f122,f244,f241,f150])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    spl8_32 <=> m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~m1_connsp_2(u1_struct_0(sK2),sK3,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_32),
% 0.21/0.49    inference(resolution,[],[f284,f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f95])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) | spl8_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f283])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~spl8_32 | ~spl8_33 | ~spl8_22 | ~spl8_5 | ~spl8_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f281,f247,f122,f200,f286,f283])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    spl8_29 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5) | ~m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_connsp_2(sK7(sK3,sK5,u1_struct_0(sK2)),sK3,sK5) | ~m1_subset_1(sK7(sK3,sK5,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl8_5 | ~spl8_29)),
% 0.21/0.49    inference(resolution,[],[f248,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5) | ~m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl8_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f247])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~spl8_19 | ~spl8_18 | ~spl8_11 | spl8_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f276,f241,f146,f174,f178])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_11 | spl8_27)),
% 0.21/0.49    inference(resolution,[],[f275,f147])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_27),
% 0.21/0.49    inference(resolution,[],[f242,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~v2_pre_topc(sK3) | spl8_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f241])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~spl8_18 | ~spl8_11 | spl8_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f271,f244,f146,f174])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl8_11 | spl8_28)),
% 0.21/0.49    inference(resolution,[],[f270,f147])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_28),
% 0.21/0.49    inference(resolution,[],[f245,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~l1_pre_topc(sK3) | spl8_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f244])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ~spl8_28 | ~spl8_6 | spl8_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f263,f237,f126,f244])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | spl8_26),
% 0.21/0.49    inference(resolution,[],[f238,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | spl8_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f237])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~spl8_18 | ~spl8_13 | spl8_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f257,f234,f154,f174])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | (~spl8_13 | spl8_25)),
% 0.21/0.49    inference(resolution,[],[f255,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0) | ~spl8_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl8_25),
% 0.21/0.49    inference(resolution,[],[f235,f77])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ~l1_pre_topc(sK2) | spl8_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f234])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ~spl8_25 | ~spl8_26 | ~spl8_6 | spl8_12 | ~spl8_27 | ~spl8_28 | spl8_29 | ~spl8_22 | spl8_14 | spl8_30 | ~spl8_7 | ~spl8_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f232,f219,f130,f252,f158,f200,f247,f244,f241,f150,f126,f237,f234])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl8_24 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(X0) | ~l1_pre_topc(sK2)) ) | (~spl8_7 | ~spl8_24)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK7(sK3,X1,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(sK7(sK3,X1,u1_struct_0(sK2)),sK3,sK5) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(X0) | ~l1_pre_topc(sK2)) ) | (~spl8_7 | ~spl8_24)),
% 0.21/0.49    inference(resolution,[],[f230,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    v1_tsep_1(sK2,sK3) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_subset_1(sK5,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),sK5) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(sK7(X0,X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(sK7(X0,X1,u1_struct_0(X2)),sK3,sK5) | ~m1_subset_1(X1,u1_struct_0(X2)) | v2_struct_0(X3) | ~l1_pre_topc(X2)) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f229,f76])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X3) | ~m1_subset_1(sK7(X1,X2,u1_struct_0(X3)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,u1_struct_0(X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tmap_1(X3,sK1,k3_tmap_1(X0,sK1,sK3,X3,sK4),sK5) | ~m1_pre_topc(X3,sK3) | ~m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | ~m1_connsp_2(sK7(X1,X2,u1_struct_0(X3)),sK3,sK5) | ~m1_subset_1(X2,u1_struct_0(X3)) | v2_struct_0(X0)) ) | ~spl8_24),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~m1_subset_1(sK7(X1,X2,u1_struct_0(X3)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK5,u1_struct_0(X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tmap_1(X3,sK1,k3_tmap_1(X0,sK1,sK3,X3,sK4),sK5) | ~m1_pre_topc(X3,sK3) | ~m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | ~m1_connsp_2(sK7(X1,X2,u1_struct_0(X3)),sK3,sK5) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~l1_struct_0(X3) | v2_struct_0(X3)) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f227,f79])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v1_xboole_0(u1_struct_0(X2)) | v2_struct_0(X3) | ~m1_subset_1(sK7(X0,X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X3) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_subset_1(sK5,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),sK5) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_connsp_2(sK7(X0,X1,u1_struct_0(X2)),sK3,sK5) | ~m1_subset_1(X1,u1_struct_0(X2))) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f226,f94])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,u1_struct_0(X0)) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5) | v2_struct_0(X1) | ~m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | ~v1_tsep_1(X0,X2)) ) | ~spl8_24),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f225])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5) | v2_struct_0(X1) | ~m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r2_hidden(X3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | ~v1_tsep_1(X0,X2) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f224,f102])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(u1_struct_0(X0),X2) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5) | v2_struct_0(X1) | ~m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r2_hidden(X3,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))) ) | ~spl8_24),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f223])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5) | v2_struct_0(X1) | ~m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r2_hidden(X3,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f222,f85])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(u1_struct_0(X0),X2,X3) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_connsp_2(sK7(X2,X3,u1_struct_0(X0)),sK3,sK5) | v2_struct_0(X1) | ~m1_subset_1(sK7(X2,X3,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_24),
% 0.21/0.49    inference(resolution,[],[f220,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK7(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f95])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK7(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_connsp_2(X2,sK3,sK5) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f219])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~spl8_5 | spl8_24 | spl8_1 | ~spl8_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f216,f213,f104,f219,f122])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl8_23 <=> ! [X1,X3,X0,X2] : (~m1_connsp_2(X0,sK3,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | r1_tmap_1(sK3,sK1,sK4,X1) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_connsp_2(X2,sK3,sK5) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK5) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1))) ) | (spl8_1 | ~spl8_23)),
% 0.21/0.49    inference(resolution,[],[f214,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r1_tmap_1(sK3,sK1,sK4,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | ~m1_connsp_2(X0,sK3,X1) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2))) ) | ~spl8_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    spl8_17 | ~spl8_16 | ~spl8_15 | spl8_12 | ~spl8_8 | spl8_23 | ~spl8_9 | ~spl8_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f206,f142,f138,f213,f134,f150,f162,f166,f170])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | (~spl8_9 | ~spl8_10)),
% 0.21/0.49    inference(resolution,[],[f205,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl8_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_connsp_2(X5,X3,X4) | ~r1_tarski(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_10),
% 0.21/0.49    inference(resolution,[],[f185,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl8_22 | ~spl8_3 | ~spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f198,f118,f114,f200])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl8_3 <=> sK5 = sK6),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl8_4 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_4)),
% 0.21/0.49    inference(superposition,[],[f119,f115])).
% 0.21/0.49  % (15481)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    sK5 = sK6 | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl8_21 | ~spl8_2 | ~spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f193,f114,f107,f195])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl8_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl8_2 | ~spl8_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f111,f115])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~spl8_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f182])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    (((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f49,f48,f47,f46,f45,f44,f43])).
% 0.21/0.49  % (15480)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl8_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f178])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl8_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f174])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~spl8_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f170])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl8_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f166])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v2_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl8_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f162])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~spl8_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f158])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl8_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f154])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~spl8_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f150])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~v2_struct_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f146])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl8_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f142])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f138])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl8_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f134])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl8_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f130])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f126])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl8_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f122])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl8_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f118])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl8_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f114])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    sK5 = sK6),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl8_1 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f74,f107,f104])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~spl8_1 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f107,f104])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15487)------------------------------
% 0.21/0.49  % (15487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15487)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15487)Memory used [KB]: 11001
% 0.21/0.49  % (15487)Time elapsed: 0.060 s
% 0.21/0.49  % (15487)------------------------------
% 0.21/0.49  % (15487)------------------------------
% 0.21/0.49  % (15476)Success in time 0.136 s
%------------------------------------------------------------------------------
