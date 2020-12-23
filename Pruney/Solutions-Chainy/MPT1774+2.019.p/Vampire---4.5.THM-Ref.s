%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 598 expanded)
%              Number of leaves         :   52 ( 333 expanded)
%              Depth                    :   10
%              Number of atoms          : 1250 (10802 expanded)
%              Number of equality atoms :   40 ( 551 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f179,f184,f195,f201,f214,f220,f229,f237,f247,f253,f263,f282,f301,f302])).

fof(f302,plain,
    ( sK6 != sK7
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f301,plain,
    ( spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_15
    | ~ spl8_14
    | spl8_17
    | ~ spl8_16
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_8
    | ~ spl8_25
    | ~ spl8_10
    | ~ spl8_1
    | spl8_24 ),
    inference(avatar_split_clause,[],[f292,f177,f80,f118,f182,f110,f122,f126,f130,f142,f146,f134,f138,f162,f166,f170,f150,f154,f158])).

fof(f158,plain,
    ( spl8_20
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f154,plain,
    ( spl8_19
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f150,plain,
    ( spl8_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f170,plain,
    ( spl8_23
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f166,plain,
    ( spl8_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f162,plain,
    ( spl8_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f138,plain,
    ( spl8_15
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f134,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f146,plain,
    ( spl8_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f142,plain,
    ( spl8_16
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f130,plain,
    ( spl8_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f126,plain,
    ( spl8_12
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f122,plain,
    ( spl8_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f110,plain,
    ( spl8_8
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f182,plain,
    ( spl8_25
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f118,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f80,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f177,plain,
    ( spl8_24
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f292,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_24 ),
    inference(resolution,[],[f279,f78])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f279,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f282,plain,
    ( ~ spl8_4
    | ~ spl8_24
    | ~ spl8_25
    | spl8_17
    | ~ spl8_10
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f276,f260,f118,f146,f182,f177,f94])).

fof(f94,plain,
    ( spl8_4
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f260,plain,
    ( spl8_35
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f276,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_10
    | ~ spl8_35 ),
    inference(resolution,[],[f261,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X0)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f260])).

fof(f263,plain,
    ( ~ spl8_14
    | spl8_35
    | ~ spl8_18
    | spl8_20
    | ~ spl8_19
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f257,f212,f154,f158,f150,f260,f134])).

fof(f212,plain,
    ( spl8_30
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f257,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_19
    | ~ spl8_30 ),
    inference(resolution,[],[f213,f155])).

fof(f155,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f212])).

fof(f253,plain,
    ( ~ spl8_14
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f248,f206,f102,f150,f114,f134])).

fof(f114,plain,
    ( spl8_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f102,plain,
    ( spl8_6
  <=> v3_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f206,plain,
    ( spl8_28
  <=> ! [X2] :
        ( ~ v3_pre_topc(sK5,X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f248,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(resolution,[],[f207,f103])).

fof(f103,plain,
    ( v3_pre_topc(sK5,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f207,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(sK5,X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(sK3,X2) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f206])).

fof(f247,plain,
    ( ~ spl8_18
    | ~ spl8_14
    | spl8_33 ),
    inference(avatar_split_clause,[],[f243,f234,f134,f150])).

fof(f234,plain,
    ( spl8_33
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f243,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_14
    | spl8_33 ),
    inference(resolution,[],[f242,f135])).

fof(f135,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_33 ),
    inference(resolution,[],[f235,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f235,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_33 ),
    inference(avatar_component_clause,[],[f234])).

fof(f237,plain,
    ( ~ spl8_33
    | ~ spl8_10
    | spl8_32 ),
    inference(avatar_split_clause,[],[f230,f227,f118,f234])).

fof(f227,plain,
    ( spl8_32
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f230,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | spl8_32 ),
    inference(resolution,[],[f228,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f228,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( ~ spl8_32
    | ~ spl8_4
    | spl8_31 ),
    inference(avatar_split_clause,[],[f223,f218,f94,f227])).

fof(f218,plain,
    ( spl8_31
  <=> r1_tarski(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f223,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_4
    | spl8_31 ),
    inference(resolution,[],[f221,f95])).

fof(f95,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | spl8_31 ),
    inference(resolution,[],[f219,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f219,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK3))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( ~ spl8_31
    | spl8_29 ),
    inference(avatar_split_clause,[],[f215,f209,f218])).

fof(f209,plain,
    ( spl8_29
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f215,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK3))
    | spl8_29 ),
    inference(resolution,[],[f210,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f210,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f214,plain,
    ( spl8_28
    | ~ spl8_29
    | spl8_30
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f204,f199,f98,f212,f209,f206])).

fof(f98,plain,
    ( spl8_5
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f199,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ r2_hidden(sK6,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v3_pre_topc(sK5,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2) )
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(resolution,[],[f203,f99])).

fof(f99,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f203,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK6,X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK6,u1_struct_0(X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X2,sK3)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK6)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v3_pre_topc(X0,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3) )
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK6,X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK6,u1_struct_0(X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X2,sK3)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK6)
        | ~ r1_tarski(X0,u1_struct_0(X2))
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X0,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3) )
    | ~ spl8_27 ),
    inference(resolution,[],[f200,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(sK6,X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl8_8
    | spl8_27
    | spl8_1
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f196,f193,f80,f199,f110])).

fof(f193,plain,
    ( spl8_26
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X3)
        | r1_tmap_1(sK3,sK0,sK4,X2)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ v3_pre_topc(X2,sK3)
        | ~ r2_hidden(sK6,X2) )
    | spl8_1
    | ~ spl8_26 ),
    inference(resolution,[],[f194,f81])).

fof(f81,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f194,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tmap_1(sK3,sK0,sK4,X2)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X3)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_15
    | ~ spl8_11
    | spl8_26
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f186,f130,f126,f193,f122,f138,f162,f166,f170])).

fof(f186,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r2_hidden(X2,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2)
        | r1_tmap_1(sK3,sK0,sK4,X2)
        | ~ m1_pre_topc(sK3,X3)
        | v2_struct_0(sK3)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f185,f127])).

fof(f127,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f185,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ r1_tarski(X5,u1_struct_0(X0))
        | ~ r2_hidden(X4,X5)
        | ~ v3_pre_topc(X5,X3)
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
    inference(resolution,[],[f173,f131])).

% (30932)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f131,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f173,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(subsumption_resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f76,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f19])).

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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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

fof(f184,plain,
    ( spl8_25
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f180,f106,f90,f182])).

fof(f90,plain,
    ( spl8_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f106,plain,
    ( spl8_7
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f180,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f107,f91])).

fof(f91,plain,
    ( sK6 = sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f107,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f179,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f175,f90,f83,f177])).

fof(f83,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f175,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f87,f91])).

fof(f87,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f172,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f41,f170])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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

fof(f168,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f42,f166])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f164,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f43,f162])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f160,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f44,f158])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f156,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f45,f154])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f152,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f46,f150])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f148,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f47,f146])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f144,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f48,f142])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f49,f138])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f50,f134])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f51,f130])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f128,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f52,f126])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f53,f122])).

% (30934)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f120,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f54,f118])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f56,f110])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f59,f98])).

fof(f59,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f60,f94])).

fof(f60,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f61,f90])).

fof(f61,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f83,f80])).

fof(f62,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f63,f83,f80])).

fof(f63,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (30949)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (30946)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (30938)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (30941)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (30938)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (30945)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (30937)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f85,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f152,f156,f160,f164,f168,f172,f179,f184,f195,f201,f214,f220,f229,f237,f247,f253,f263,f282,f301,f302])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    sK6 != sK7 | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl8_20 | ~spl8_19 | ~spl8_18 | spl8_23 | ~spl8_22 | ~spl8_21 | spl8_15 | ~spl8_14 | spl8_17 | ~spl8_16 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_8 | ~spl8_25 | ~spl8_10 | ~spl8_1 | spl8_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f292,f177,f80,f118,f182,f110,f122,f126,f130,f142,f146,f134,f138,f162,f166,f170,f150,f154,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl8_20 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl8_19 <=> v2_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl8_18 <=> l1_pre_topc(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl8_23 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl8_22 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl8_21 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl8_15 <=> v2_struct_0(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl8_14 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl8_17 <=> v2_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl8_16 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl8_13 <=> v1_funct_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl8_12 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl8_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl8_8 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl8_25 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl8_10 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl8_24 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,sK4,sK6) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_24),
% 0.21/0.50    inference(resolution,[],[f279,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f177])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    ~spl8_4 | ~spl8_24 | ~spl8_25 | spl8_17 | ~spl8_10 | ~spl8_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f276,f260,f118,f146,f182,f177,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl8_4 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl8_35 <=> ! [X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(sK2)) | (~spl8_10 | ~spl8_35)),
% 0.21/0.50    inference(resolution,[],[f261,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK3) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(X0))) ) | ~spl8_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f260])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ~spl8_14 | spl8_35 | ~spl8_18 | spl8_20 | ~spl8_19 | ~spl8_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f257,f212,f154,f158,f150,f260,f134])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    spl8_30 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK1) | ~r1_tarski(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | (~spl8_19 | ~spl8_30)),
% 0.21/0.50    inference(resolution,[],[f213,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    v2_pre_topc(sK1) | ~spl8_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3)) ) | ~spl8_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f212])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~spl8_14 | ~spl8_9 | ~spl8_18 | ~spl8_6 | ~spl8_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f248,f206,f102,f150,f114,f134])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl8_9 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl8_6 <=> v3_pre_topc(sK5,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    spl8_28 <=> ! [X2] : (~v3_pre_topc(sK5,X2) | ~l1_pre_topc(X2) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(sK3,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | (~spl8_6 | ~spl8_28)),
% 0.21/0.50    inference(resolution,[],[f207,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    v3_pre_topc(sK5,sK1) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X2] : (~v3_pre_topc(sK5,X2) | ~l1_pre_topc(X2) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(sK3,X2)) ) | ~spl8_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f206])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~spl8_18 | ~spl8_14 | spl8_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f243,f234,f134,f150])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    spl8_33 <=> l1_pre_topc(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~l1_pre_topc(sK1) | (~spl8_14 | spl8_33)),
% 0.21/0.50    inference(resolution,[],[f242,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1) | ~spl8_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_33),
% 0.21/0.50    inference(resolution,[],[f235,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ~l1_pre_topc(sK3) | spl8_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f234])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ~spl8_33 | ~spl8_10 | spl8_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f227,f118,f234])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl8_32 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | spl8_32),
% 0.21/0.50    inference(resolution,[],[f228,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | spl8_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f227])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ~spl8_32 | ~spl8_4 | spl8_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f218,f94,f227])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    spl8_31 <=> r1_tarski(sK5,u1_struct_0(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | (~spl8_4 | spl8_31)),
% 0.21/0.50    inference(resolution,[],[f221,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK3))) ) | spl8_31),
% 0.21/0.50    inference(resolution,[],[f219,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~r1_tarski(sK5,u1_struct_0(sK3)) | spl8_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f218])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~spl8_31 | spl8_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f215,f209,f218])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl8_29 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ~r1_tarski(sK5,u1_struct_0(sK3)) | spl8_29),
% 0.21/0.50    inference(resolution,[],[f210,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | spl8_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f209])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    spl8_28 | ~spl8_29 | spl8_30 | ~spl8_5 | ~spl8_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f204,f199,f98,f212,f209,f206])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl8_5 <=> r2_hidden(sK6,sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl8_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(X1)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(sK5,X2) | ~m1_pre_topc(sK3,X2) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) ) | (~spl8_5 | ~spl8_27)),
% 0.21/0.50    inference(resolution,[],[f203,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    r2_hidden(sK6,sK5) | ~spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK6,X0) | v2_struct_0(X1) | ~m1_subset_1(sK6,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK6) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v3_pre_topc(X0,X3) | ~m1_pre_topc(sK3,X3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) ) | ~spl8_27),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK6,X0) | v2_struct_0(X1) | ~m1_subset_1(sK6,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK6) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,X3) | ~m1_pre_topc(sK3,X3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) ) | ~spl8_27),
% 0.21/0.50    inference(resolution,[],[f200,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v3_pre_topc(X2,sK3) | ~r2_hidden(sK6,X2) | v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f199])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ~spl8_8 | spl8_27 | spl8_1 | ~spl8_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f196,f193,f80,f199,f110])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    spl8_26 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,u1_struct_0(X1)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X3) | r1_tmap_1(sK3,sK0,sK4,X2) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK6) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(sK6,X2)) ) | (spl8_1 | ~spl8_26)),
% 0.21/0.50    inference(resolution,[],[f194,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,sK4,sK6) | spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_tmap_1(sK3,sK0,sK4,X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X3) | ~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(X2,X0)) ) | ~spl8_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f193])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_15 | ~spl8_11 | spl8_26 | ~spl8_12 | ~spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f186,f130,f126,f193,f122,f138,f162,f166,f170])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X3,sK0,sK3,X1,sK4),X2) | r1_tmap_1(sK3,sK0,sK4,X2) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | (~spl8_12 | ~spl8_13)),
% 0.21/0.50    inference(resolution,[],[f185,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~r1_tarski(X5,u1_struct_0(X0)) | ~r2_hidden(X4,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_13),
% 0.21/0.50    inference(resolution,[],[f173,f131])).
% 0.21/0.50  % (30932)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    v1_funct_1(sK4) | ~spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl8_25 | ~spl8_3 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f106,f90,f182])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl8_3 <=> sK6 = sK7),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl8_7 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_7)),
% 0.21/0.50    inference(superposition,[],[f107,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    sK6 = sK7 | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl8_24 | ~spl8_2 | ~spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f175,f90,f83,f177])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | (~spl8_2 | ~spl8_3)),
% 0.21/0.50    inference(forward_demodulation,[],[f87,f91])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl8_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f170])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl8_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f166])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl8_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f162])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~spl8_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f158])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl8_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f154])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl8_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f150])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~spl8_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f146])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl8_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f142])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~spl8_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f138])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl8_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f134])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f130])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl8_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f126])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f122])).
% 0.21/0.50  % (30934)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f118])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl8_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f114])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f110])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f106])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f102])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v3_pre_topc(sK5,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f98])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(sK6,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f94])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f90])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    sK6 = sK7),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl8_1 | spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f83,f80])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ~spl8_1 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f83,f80])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30938)------------------------------
% 0.21/0.50  % (30938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30938)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30938)Memory used [KB]: 11001
% 0.21/0.50  % (30938)Time elapsed: 0.076 s
% 0.21/0.50  % (30938)------------------------------
% 0.21/0.50  % (30938)------------------------------
% 0.21/0.50  % (30939)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (30931)Success in time 0.143 s
%------------------------------------------------------------------------------
