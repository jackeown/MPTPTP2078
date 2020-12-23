%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 599 expanded)
%              Number of leaves         :   47 ( 336 expanded)
%              Depth                    :   10
%              Number of atoms          : 1221 (10542 expanded)
%              Number of equality atoms :   32 ( 527 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f131,f135,f139,f143,f147,f151,f155,f162,f167,f178,f184,f196,f203,f208,f215,f223,f229,f241,f247,f250,f251])).

fof(f251,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_17
    | spl8_15
    | ~ spl8_14
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_8
    | ~ spl8_25
    | spl8_33
    | ~ spl8_1
    | spl8_24 ),
    inference(avatar_split_clause,[],[f242,f160,f63,f233,f165,f93,f101,f105,f109,f113,f117,f121,f129,f133,f137,f141,f145,f149,f153])).

fof(f153,plain,
    ( spl8_23
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f149,plain,
    ( spl8_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f145,plain,
    ( spl8_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f141,plain,
    ( spl8_20
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f137,plain,
    ( spl8_19
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f133,plain,
    ( spl8_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f129,plain,
    ( spl8_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f121,plain,
    ( spl8_15
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f117,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f113,plain,
    ( spl8_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f109,plain,
    ( spl8_12
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f105,plain,
    ( spl8_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f101,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f93,plain,
    ( spl8_8
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f165,plain,
    ( spl8_25
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f233,plain,
    ( spl8_33
  <=> ! [X1] :
        ( ~ m1_connsp_2(X1,sK3,sK6)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X1,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f63,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f160,plain,
    ( spl8_24
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
        | ~ m1_connsp_2(X0,sK3,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl8_24 ),
    inference(resolution,[],[f240,f157])).

fof(f157,plain,(
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
    inference(subsumption_resolution,[],[f61,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f240,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f250,plain,
    ( spl8_15
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_9
    | ~ spl8_8
    | ~ spl8_6
    | ~ spl8_5
    | spl8_35 ),
    inference(avatar_split_clause,[],[f248,f245,f81,f85,f93,f97,f191,f188,f121])).

fof(f188,plain,
    ( spl8_28
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f191,plain,
    ( spl8_29
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f97,plain,
    ( spl8_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f85,plain,
    ( spl8_6
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f81,plain,
    ( spl8_5
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f245,plain,
    ( spl8_35
  <=> m1_connsp_2(sK5,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f248,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl8_35 ),
    inference(resolution,[],[f246,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f246,plain,
    ( ~ m1_connsp_2(sK5,sK3,sK6)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( ~ spl8_35
    | ~ spl8_9
    | ~ spl8_4
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f243,f233,f77,f97,f245])).

fof(f77,plain,
    ( spl8_4
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_connsp_2(sK5,sK3,sK6)
    | ~ spl8_4
    | ~ spl8_33 ),
    inference(resolution,[],[f234,f78])).

fof(f78,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f234,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X1,sK3,sK6) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f233])).

fof(f241,plain,
    ( ~ spl8_24
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f239,f73,f66,f160])).

fof(f66,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f73,plain,
    ( spl8_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f239,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f67,f74])).

fof(f74,plain,
    ( sK6 = sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f67,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f229,plain,
    ( ~ spl8_22
    | spl8_23
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_24
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f224,f220,f160,f145,f117,f153,f149])).

fof(f220,plain,
    ( spl8_32
  <=> ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_24
    | ~ spl8_32 ),
    inference(resolution,[],[f221,f161])).

fof(f161,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( spl8_17
    | ~ spl8_25
    | spl8_32
    | ~ spl8_10
    | ~ spl8_4
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f216,f212,f77,f101,f220,f165,f129])).

fof(f212,plain,
    ( spl8_31
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK3)
        | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_4
    | ~ spl8_31 ),
    inference(resolution,[],[f213,f78])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f212])).

fof(f215,plain,
    ( ~ spl8_9
    | spl8_31
    | ~ spl8_6
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f209,f194,f81,f85,f212,f97])).

fof(f194,plain,
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
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f209,plain,
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
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_5
    | ~ spl8_30 ),
    inference(resolution,[],[f195,f82])).

fof(f82,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f195,plain,
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
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f194])).

fof(f208,plain,
    ( ~ spl8_21
    | ~ spl8_14
    | spl8_29 ),
    inference(avatar_split_clause,[],[f205,f191,f117,f145])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_14
    | spl8_29 ),
    inference(resolution,[],[f204,f118])).

fof(f118,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_29 ),
    inference(resolution,[],[f192,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f192,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f191])).

fof(f203,plain,
    ( ~ spl8_22
    | ~ spl8_21
    | ~ spl8_14
    | spl8_28 ),
    inference(avatar_split_clause,[],[f198,f188,f117,f145,f149])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_14
    | spl8_28 ),
    inference(resolution,[],[f197,f118])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_28 ),
    inference(resolution,[],[f189,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f189,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f188])).

fof(f196,plain,
    ( spl8_15
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_8
    | spl8_30
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f186,f182,f194,f93,f191,f188,f121])).

fof(f182,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | ~ m1_connsp_2(X2,sK3,sK6)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
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
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6)
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
    inference(resolution,[],[f183,f55])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X2,sK3,sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | v2_struct_0(X0)
        | ~ r1_tarski(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f182])).

fof(f184,plain,
    ( ~ spl8_8
    | spl8_27
    | spl8_1
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f179,f176,f63,f182,f93])).

fof(f176,plain,
    ( spl8_26
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
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_connsp_2(X2,sK3,sK6)
        | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X1)) )
    | spl8_1
    | ~ spl8_26 ),
    inference(resolution,[],[f177,f64])).

fof(f64,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f177,plain,
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
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_15
    | ~ spl8_11
    | spl8_26
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f169,f113,f109,f176,f105,f121,f133,f137,f141])).

fof(f169,plain,
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
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f168,f110])).

fof(f110,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f168,plain,
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
    inference(resolution,[],[f156,f114])).

fof(f114,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f156,plain,(
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
    inference(subsumption_resolution,[],[f60,f59])).

fof(f60,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f167,plain,
    ( spl8_25
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f163,f89,f73,f165])).

fof(f89,plain,
    ( spl8_7
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f163,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f90,f74])).

fof(f90,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f162,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f158,f73,f66,f160])).

fof(f158,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f70,f74])).

fof(f70,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f155,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f31,f153])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK1,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK3)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f28,f27,f26,f25,f24,f23,f22,f21])).

% (16352)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (16358)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (16353)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X1,X4,X6) )
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
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

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X1,X4,X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X1,X4,X6) )
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
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK1,X4,X6) )
                              & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK1,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X3)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
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

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK1,X4,X6) )
                            & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK1,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(X2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X3)
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(X2,X3)
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
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK1,X4,X6) )
                          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK1,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X3)
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK1,X4,X6) )
                        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK1,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X3)
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK1,X4,X6) )
                      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK1,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,sK3)
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK1,X4,X6) )
                    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK1,X4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,sK3)
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK1,sK4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,sK3)
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
                & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK1,sK4,X6) )
                & X6 = X7
                & r1_tarski(X5,u1_struct_0(sK2))
                & r2_hidden(X6,X5)
                & v3_pre_topc(X5,sK3)
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
              & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK1,sK4,X6) )
              & X6 = X7
              & r1_tarski(sK5,u1_struct_0(sK2))
              & r2_hidden(X6,sK5)
              & v3_pre_topc(sK5,sK3)
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK1,sK4,X6) )
            & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK1,sK4,X6) )
            & X6 = X7
            & r1_tarski(sK5,u1_struct_0(sK2))
            & r2_hidden(X6,sK5)
            & v3_pre_topc(sK5,sK3)
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK1,sK4,sK6) )
          & sK6 = X7
          & r1_tarski(sK5,u1_struct_0(sK2))
          & r2_hidden(sK6,sK5)
          & v3_pre_topc(sK5,sK3)
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK1,sK4,sK6) )
        & sK6 = X7
        & r1_tarski(sK5,u1_struct_0(sK2))
        & r2_hidden(sK6,sK5)
        & v3_pre_topc(sK5,sK3)
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK1,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK1,sK4,sK6) )
      & sK6 = sK7
      & r1_tarski(sK5,u1_struct_0(sK2))
      & r2_hidden(sK6,sK5)
      & v3_pre_topc(sK5,sK3)
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,X4,X6) )
                                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X1,X4,X6) )
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f151,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f32,f149])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f147,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f33,f145])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f34,f141])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f35,f137])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f135,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f36,f133])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f37,f129])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f39,f121])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f40,f117])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f115,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f41,f113])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f111,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f43,f105])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f47,f89])).

fof(f47,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f49,f81])).

fof(f49,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f50,f77])).

fof(f50,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f51,f73])).

fof(f51,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f52,f66,f63])).

fof(f52,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f53,f66,f63])).

fof(f53,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16357)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (16357)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (16365)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f68,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f131,f135,f139,f143,f147,f151,f155,f162,f167,f178,f184,f196,f203,f208,f215,f223,f229,f241,f247,f250,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_20 | ~spl8_19 | ~spl8_18 | spl8_17 | spl8_15 | ~spl8_14 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | ~spl8_8 | ~spl8_25 | spl8_33 | ~spl8_1 | spl8_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f242,f160,f63,f233,f165,f93,f101,f105,f109,f113,f117,f121,f129,f133,f137,f141,f145,f149,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl8_23 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl8_22 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl8_21 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl8_20 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl8_19 <=> v2_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl8_18 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl8_17 <=> v2_struct_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl8_15 <=> v2_struct_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl8_14 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl8_13 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl8_12 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl8_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl8_10 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl8_8 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl8_25 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    spl8_33 <=> ! [X1] : (~m1_connsp_2(X1,sK3,sK6) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X1,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl8_1 <=> r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl8_24 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_connsp_2(X0,sK3,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl8_24),
% 0.21/0.51    inference(resolution,[],[f240,f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f61,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | spl8_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    spl8_15 | ~spl8_28 | ~spl8_29 | ~spl8_9 | ~spl8_8 | ~spl8_6 | ~spl8_5 | spl8_35),
% 0.21/0.51    inference(avatar_split_clause,[],[f248,f245,f81,f85,f93,f97,f191,f188,f121])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl8_28 <=> v2_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl8_29 <=> l1_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl8_9 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl8_6 <=> v3_pre_topc(sK5,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl8_5 <=> r2_hidden(sK6,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl8_35 <=> m1_connsp_2(sK5,sK3,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    ~r2_hidden(sK6,sK5) | ~v3_pre_topc(sK5,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl8_35),
% 0.21/0.51    inference(resolution,[],[f246,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ~m1_connsp_2(sK5,sK3,sK6) | spl8_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f245])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ~spl8_35 | ~spl8_9 | ~spl8_4 | ~spl8_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f243,f233,f77,f97,f245])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl8_4 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(sK5,sK3,sK6) | (~spl8_4 | ~spl8_33)),
% 0.21/0.51    inference(resolution,[],[f234,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X1,sK3,sK6)) ) | ~spl8_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f233])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~spl8_24 | spl8_2 | ~spl8_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f73,f66,f160])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl8_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl8_3 <=> sK6 = sK7),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | (spl8_2 | ~spl8_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    sK6 = sK7 | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    ~spl8_22 | spl8_23 | ~spl8_14 | ~spl8_21 | ~spl8_24 | ~spl8_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f224,f220,f160,f145,f117,f153,f149])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    spl8_32 <=> ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | (~spl8_24 | ~spl8_32)),
% 0.21/0.51    inference(resolution,[],[f221,f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl8_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0)) ) | ~spl8_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f220])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl8_17 | ~spl8_25 | spl8_32 | ~spl8_10 | ~spl8_4 | ~spl8_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f216,f212,f77,f101,f220,f165,f129])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl8_31 <=> ! [X1,X0] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | ~r1_tarski(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | (~spl8_4 | ~spl8_31)),
% 0.21/0.51    inference(resolution,[],[f213,f78])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | ~m1_subset_1(sK6,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1)) ) | ~spl8_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f212])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~spl8_9 | spl8_31 | ~spl8_6 | ~spl8_5 | ~spl8_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f209,f194,f81,f85,f212,f97])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    spl8_30 <=> ! [X1,X0,X2] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~v3_pre_topc(X2,sK3) | ~r2_hidden(sK6,X2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_pre_topc(sK5,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(sK5,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3)) ) | (~spl8_5 | ~spl8_30)),
% 0.21/0.51    inference(resolution,[],[f195,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    r2_hidden(sK6,sK5) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | ~m1_pre_topc(X0,sK3)) ) | ~spl8_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f194])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~spl8_21 | ~spl8_14 | spl8_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f205,f191,f117,f145])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | (~spl8_14 | spl8_29)),
% 0.21/0.51    inference(resolution,[],[f204,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK0) | ~spl8_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_29),
% 0.21/0.51    inference(resolution,[],[f192,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | spl8_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f191])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~spl8_22 | ~spl8_21 | ~spl8_14 | spl8_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f198,f188,f117,f145,f149])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_14 | spl8_28)),
% 0.21/0.52    inference(resolution,[],[f197,f118])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_28),
% 0.21/0.52    inference(resolution,[],[f189,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~v2_pre_topc(sK3) | spl8_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f188])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl8_15 | ~spl8_28 | ~spl8_29 | ~spl8_8 | spl8_30 | ~spl8_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f186,f182,f194,f93,f191,f188,f121])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    spl8_27 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_27),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK6) | v2_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r2_hidden(sK6,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl8_27),
% 0.21/0.52    inference(resolution,[],[f183,f55])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,sK3,sK6) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | v2_struct_0(X0) | ~r1_tarski(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f182])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~spl8_8 | spl8_27 | spl8_1 | ~spl8_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f179,f176,f63,f182,f93])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl8_26 <=> ! [X1,X3,X0,X2] : (~m1_connsp_2(X0,sK3,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | r1_tmap_1(sK3,sK1,sK4,X1) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_connsp_2(X2,sK3,sK6) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X0,sK1,sK3,X1,sK4),sK6) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X1)) | ~r1_tarski(X2,u1_struct_0(X1))) ) | (spl8_1 | ~spl8_26)),
% 0.21/0.52    inference(resolution,[],[f177,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~r1_tmap_1(sK3,sK1,sK4,sK6) | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_tmap_1(sK3,sK1,sK4,X1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X2) | ~m1_pre_topc(sK3,X3) | ~m1_connsp_2(X0,sK3,X1) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X2))) ) | ~spl8_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f176])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl8_20 | ~spl8_19 | ~spl8_18 | spl8_15 | ~spl8_11 | spl8_26 | ~spl8_12 | ~spl8_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f169,f113,f109,f176,f105,f121,f133,f137,f141])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,sK3,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~r1_tmap_1(X2,sK1,k3_tmap_1(X3,sK1,sK3,X2,sK4),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | (~spl8_12 | ~spl8_13)),
% 0.21/0.52    inference(resolution,[],[f168,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl8_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_connsp_2(X5,X3,X4) | ~r1_tarski(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_13),
% 0.21/0.52    inference(resolution,[],[f156,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    v1_funct_1(sK4) | ~spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f59])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl8_25 | ~spl8_3 | ~spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f163,f89,f73,f165])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl8_7 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_7)),
% 0.21/0.52    inference(superposition,[],[f90,f74])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl8_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl8_24 | ~spl8_2 | ~spl8_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f158,f73,f66,f160])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | (~spl8_2 | ~spl8_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f70,f74])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~spl8_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f153])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ((((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f28,f27,f26,f25,f24,f23,f22,f21])).
% 0.21/0.52  % (16352)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16358)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (16353)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,X4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,X6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X7] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK3) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X1,X4,X6) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f149])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    spl8_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f145])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ~spl8_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f141])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl8_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f137])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f133])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~spl8_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f129])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~spl8_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f121])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl8_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f117])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f113])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl8_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f109])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl8_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f105])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f101])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f97])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f93])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl8_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f89])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f85])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v3_pre_topc(sK5,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f81])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    r2_hidden(sK6,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f77])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f73])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    sK6 = sK7),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl8_1 | spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f52,f66,f63])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f66,f63])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (16357)------------------------------
% 0.21/0.53  % (16357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16357)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (16357)Memory used [KB]: 10874
% 0.21/0.53  % (16357)Time elapsed: 0.075 s
% 0.21/0.53  % (16357)------------------------------
% 0.21/0.53  % (16357)------------------------------
% 0.21/0.53  % (16350)Success in time 0.17 s
%------------------------------------------------------------------------------
