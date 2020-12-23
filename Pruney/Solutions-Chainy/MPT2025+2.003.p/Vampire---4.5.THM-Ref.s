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
% DateTime   : Thu Dec  3 13:23:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 538 expanded)
%              Number of leaves         :   42 ( 265 expanded)
%              Depth                    :   14
%              Number of atoms          :  929 (3266 expanded)
%              Number of equality atoms :   25 ( 175 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f130,f135,f140,f145,f150,f158,f166,f172,f180,f185,f200,f205,f211,f219,f226,f233,f237,f245])).

fof(f245,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f243,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f243,plain,
    ( v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f242,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl10_2
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f242,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f241,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl10_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f240,f228])).

fof(f228,plain,
    ( m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK6(X0,X1,X2))
                    & r2_hidden(X2,sK6(X0,X1,X2))
                    & v3_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK6(X0,X1,X2))
        & r2_hidden(X2,sK6(X0,X1,X2))
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f139,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl10_11
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f144,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK2,sK5))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_12
  <=> r2_hidden(sK3,k2_pre_topc(sK2,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f123,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_8
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f240,plain,
    ( ~ m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f239,f123])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f238,f171])).

fof(f171,plain,
    ( v3_pre_topc(sK6(sK2,sK5,sK3),sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl10_16
  <=> v3_pre_topc(sK6(sK2,sK5,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f238,plain,
    ( ~ v3_pre_topc(sK6(sK2,sK5,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f235,f179])).

fof(f179,plain,
    ( r2_hidden(sK3,sK6(sK2,sK5,sK3))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl10_17
  <=> r2_hidden(sK3,sK6(sK2,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f235,plain,
    ( ~ r2_hidden(sK3,sK6(sK2,sK5,sK3))
    | ~ v3_pre_topc(sK6(sK2,sK5,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl10_24 ),
    inference(resolution,[],[f232,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f232,plain,
    ( ~ m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3)
    | spl10_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl10_24
  <=> m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f237,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(subsumption_resolution,[],[f234,f228])).

fof(f234,plain,
    ( ~ m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_17
    | spl10_24 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f123,f179,f171,f232,f71])).

fof(f233,plain,
    ( ~ spl10_24
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_22
    | spl10_23 ),
    inference(avatar_split_clause,[],[f227,f223,f216,f132,f121,f230])).

fof(f132,plain,
    ( spl10_10
  <=> r2_hidden(sK3,k10_yellow_6(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f216,plain,
    ( spl10_22
  <=> sP0(sK4,sK2,k10_yellow_6(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f223,plain,
    ( spl10_23
  <=> r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f227,plain,
    ( ~ m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_22
    | spl10_23 ),
    inference(unit_resulting_resolution,[],[f134,f218,f123,f225,f74])).

fof(f74,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ m1_connsp_2(X8,X1,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | r1_waybel_0(X1,X0,X8) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r1_waybel_0(X1,X0,sK8(X0,X1,X2))
              & m1_connsp_2(sK8(X0,X1,X2),X1,sK7(X0,X1,X2)) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X1,X0,X5)
                | ~ m1_connsp_2(X5,X1,sK7(X0,X1,X2)) )
            | r2_hidden(sK7(X0,X1,X2),X2) )
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ( ~ r1_waybel_0(X1,X0,sK9(X0,X1,X6))
                  & m1_connsp_2(sK9(X0,X1,X6),X1,X6) ) )
              & ( ! [X8] :
                    ( r1_waybel_0(X1,X0,X8)
                    | ~ m1_connsp_2(X8,X1,X6) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X1,X0,X4)
                & m1_connsp_2(X4,X1,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X1,X0,X5)
                | ~ m1_connsp_2(X5,X1,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X1,X0,X4)
              & m1_connsp_2(X4,X1,sK7(X0,X1,X2)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X1,X0,X5)
              | ~ m1_connsp_2(X5,X1,sK7(X0,X1,X2)) )
          | r2_hidden(sK7(X0,X1,X2),X2) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X1,X0,X4)
          & m1_connsp_2(X4,X1,sK7(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X1,X0,sK8(X0,X1,X2))
        & m1_connsp_2(sK8(X0,X1,X2),X1,sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X1,X0,X7)
          & m1_connsp_2(X7,X1,X6) )
     => ( ~ r1_waybel_0(X1,X0,sK9(X0,X1,X6))
        & m1_connsp_2(sK9(X0,X1,X6),X1,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X1,X0,X4)
                  & m1_connsp_2(X4,X1,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X5] :
                  ( r1_waybel_0(X1,X0,X5)
                  | ~ m1_connsp_2(X5,X1,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ? [X7] :
                    ( ~ r1_waybel_0(X1,X0,X7)
                    & m1_connsp_2(X7,X1,X6) ) )
              & ( ! [X8] :
                    ( r1_waybel_0(X1,X0,X8)
                    | ~ m1_connsp_2(X8,X1,X6) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X1,X4)
                  & m1_connsp_2(X4,X0,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( r1_waybel_0(X0,X1,X4)
                  | ~ m1_connsp_2(X4,X0,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( ~ r1_waybel_0(X0,X1,X4)
                    & m1_connsp_2(X4,X0,X3) ) )
              & ( ! [X4] :
                    ( r1_waybel_0(X0,X1,X4)
                    | ~ m1_connsp_2(X4,X0,X3) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X1,X4)
                  & m1_connsp_2(X4,X0,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( r1_waybel_0(X0,X1,X4)
                  | ~ m1_connsp_2(X4,X0,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( ~ r1_waybel_0(X0,X1,X4)
                    & m1_connsp_2(X4,X0,X3) ) )
              & ( ! [X4] :
                    ( r1_waybel_0(X0,X1,X4)
                    | ~ m1_connsp_2(X4,X0,X3) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ! [X4] :
                ( r1_waybel_0(X0,X1,X4)
                | ~ m1_connsp_2(X4,X0,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f225,plain,
    ( ~ r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f223])).

fof(f218,plain,
    ( sP0(sK4,sK2,k10_yellow_6(sK2,sK4))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f134,plain,
    ( r2_hidden(sK3,k10_yellow_6(sK2,sK4))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f226,plain,
    ( ~ spl10_23
    | spl10_1
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_14
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f186,f182,f155,f127,f116,f111,f106,f101,f86,f223])).

fof(f101,plain,
    ( spl10_4
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f106,plain,
    ( spl10_5
  <=> v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f111,plain,
    ( spl10_6
  <=> v7_waybel_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f116,plain,
    ( spl10_7
  <=> l1_waybel_0(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f127,plain,
    ( spl10_9
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f155,plain,
    ( spl10_14
  <=> r1_waybel_0(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f182,plain,
    ( spl10_18
  <=> r1_xboole_0(sK5,sK6(sK2,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f186,plain,
    ( ~ r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3))
    | spl10_1
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_14
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f88,f129,f103,f108,f184,f118,f157,f113,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ r1_xboole_0(X2,X3)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(f113,plain,
    ( v7_waybel_0(sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f157,plain,
    ( r1_waybel_0(sK2,sK4,sK5)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f118,plain,
    ( l1_waybel_0(sK4,sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f184,plain,
    ( r1_xboole_0(sK5,sK6(sK2,sK5,sK3))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f108,plain,
    ( v4_orders_2(sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f103,plain,
    ( ~ v2_struct_0(sK4)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f129,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f219,plain,
    ( spl10_22
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f212,f208,f216])).

fof(f208,plain,
    ( spl10_21
  <=> sP1(k10_yellow_6(sK2,sK4),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f212,plain,
    ( sP0(sK4,sK2,k10_yellow_6(sK2,sK4))
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f210,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ sP1(k10_yellow_6(X1,X2),X1,X2)
      | sP0(X2,X1,k10_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k10_yellow_6(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( k10_yellow_6(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k10_yellow_6(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ( ( k10_yellow_6(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k10_yellow_6(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( k10_yellow_6(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f210,plain,
    ( sP1(k10_yellow_6(sK2,sK4),sK2,sK4)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( spl10_21
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f192,f163,f116,f111,f106,f101,f96,f91,f86,f208])).

fof(f163,plain,
    ( spl10_15
  <=> m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f192,plain,
    ( sP1(k10_yellow_6(sK2,sK4),sK2,sK4)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f165,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | sP1(X2,X0,X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f29,f28])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f165,plain,
    ( m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f205,plain,
    ( spl10_20
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f191,f137,f116,f111,f106,f101,f96,f91,f86,f202])).

fof(f202,plain,
    ( spl10_20
  <=> sP1(sK5,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f191,plain,
    ( sP1(sK5,sK2,sK4)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f139,f81])).

fof(f200,plain,
    ( ~ spl10_19
    | spl10_1
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f187,f155,f127,f116,f111,f106,f101,f86,f197])).

fof(f197,plain,
    ( spl10_19
  <=> r1_xboole_0(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f187,plain,
    ( ~ r1_xboole_0(sK5,sK5)
    | spl10_1
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f88,f129,f103,f108,f118,f157,f157,f113,f69])).

fof(f185,plain,
    ( spl10_18
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f175,f142,f137,f121,f96,f86,f182])).

fof(f175,plain,
    ( r1_xboole_0(sK5,sK6(sK2,sK5,sK3))
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,sK6(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f180,plain,
    ( spl10_17
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f174,f142,f137,f121,f96,f86,f177])).

fof(f174,plain,
    ( r2_hidden(sK3,sK6(sK2,sK5,sK3))
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK6(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f172,plain,
    ( spl10_16
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(avatar_split_clause,[],[f167,f142,f137,f121,f96,f86,f169])).

fof(f167,plain,
    ( v3_pre_topc(sK6(sK2,sK5,sK3),sK2)
    | spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_11
    | spl10_12 ),
    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,
    ( spl10_15
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f161,f116,f111,f106,f101,f96,f91,f86,f163])).

fof(f161,plain,
    ( m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f158,plain,
    ( spl10_14
    | spl10_1
    | spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f153,f147,f127,f116,f101,f86,f155])).

fof(f147,plain,
    ( spl10_13
  <=> k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f153,plain,
    ( r1_waybel_0(sK2,sK4,sK5)
    | spl10_1
    | spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_13 ),
    inference(forward_demodulation,[],[f151,f149])).

fof(f149,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f151,plain,
    ( r1_waybel_0(sK2,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)))
    | spl10_1
    | spl10_4
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f88,f129,f103,f118,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f150,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f60,f147])).

fof(f60,plain,(
    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK2,sK5))
    & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & r2_hidden(sK3,k10_yellow_6(sK2,sK4))
    & l1_waybel_0(sK4,sK2)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k10_yellow_6(X0,X2))
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(sK2,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X1,k10_yellow_6(sK2,X2))
              & l1_waybel_0(X2,sK2)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X1,k2_pre_topc(sK2,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & r2_hidden(X1,k10_yellow_6(sK2,X2))
            & l1_waybel_0(X2,sK2)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(sK3,k2_pre_topc(sK2,X3))
              & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & r2_hidden(sK3,k10_yellow_6(sK2,X2))
          & l1_waybel_0(X2,sK2)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(sK3,k2_pre_topc(sK2,X3))
            & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(sK3,k10_yellow_6(sK2,X2))
        & l1_waybel_0(X2,sK2)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(sK3,k2_pre_topc(sK2,X3))
          & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & r2_hidden(sK3,k10_yellow_6(sK2,sK4))
      & l1_waybel_0(sK4,sK2)
      & v7_waybel_0(sK4)
      & v4_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK3,k2_pre_topc(sK2,X3))
        & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ r2_hidden(sK3,k2_pre_topc(sK2,sK5))
      & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r2_hidden(X1,k10_yellow_6(X0,X2))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                       => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( r2_hidden(X1,k10_yellow_6(X0,X2))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                     => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).

fof(f145,plain,(
    ~ spl10_12 ),
    inference(avatar_split_clause,[],[f61,f142])).

fof(f61,plain,(
    ~ r2_hidden(sK3,k2_pre_topc(sK2,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f140,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f59,f137])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f135,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f58,f132])).

fof(f58,plain,(
    r2_hidden(sK3,k10_yellow_6(sK2,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f130,plain,
    ( spl10_9
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f125,f96,f127])).

fof(f125,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f124,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f119,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f57,f116])).

fof(f57,plain,(
    l1_waybel_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f55,f106])).

fof(f55,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f52,f96])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f50,f86])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (23429)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (23422)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (23427)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (23429)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f130,f135,f140,f145,f150,f158,f166,f172,f180,f185,f200,f205,f211,f219,f226,f233,f237,f245])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v2_struct_0(sK2) | spl10_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl10_1 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    v2_struct_0(sK2) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f242,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v2_pre_topc(sK2) | ~spl10_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl10_2 <=> v2_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f241,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    l1_pre_topc(sK2) | ~spl10_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl10_3 <=> l1_pre_topc(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK6(X0,X1,X2)) & r2_hidden(X2,sK6(X0,X1,X2)) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK6(X0,X1,X2)) & r2_hidden(X2,sK6(X0,X1,X2)) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl10_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl10_11 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK2,sK5)) | spl10_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl10_12 <=> r2_hidden(sK3,k2_pre_topc(sK2,sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl10_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl10_8 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_8 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f239,f123])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f238,f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    v3_pre_topc(sK6(sK2,sK5,sK3),sK2) | ~spl10_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl10_16 <=> v3_pre_topc(sK6(sK2,sK5,sK3),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ~v3_pre_topc(sK6(sK2,sK5,sK3),sK2) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f235,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    r2_hidden(sK3,sK6(sK2,sK5,sK3)) | ~spl10_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl10_17 <=> r2_hidden(sK3,sK6(sK2,sK5,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK6(sK2,sK5,sK3)) | ~v3_pre_topc(sK6(sK2,sK5,sK3),sK2) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl10_24),
% 0.21/0.48    inference(resolution,[],[f232,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3) | spl10_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    spl10_24 <=> m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f228])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~m1_subset_1(sK6(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_8 | ~spl10_16 | ~spl10_17 | spl10_24)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f93,f98,f123,f179,f171,f232,f71])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~spl10_24 | ~spl10_8 | ~spl10_10 | ~spl10_22 | spl10_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f227,f223,f216,f132,f121,f230])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl10_10 <=> r2_hidden(sK3,k10_yellow_6(sK2,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    spl10_22 <=> sP0(sK4,sK2,k10_yellow_6(sK2,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl10_23 <=> r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~m1_connsp_2(sK6(sK2,sK5,sK3),sK2,sK3) | (~spl10_8 | ~spl10_10 | ~spl10_22 | spl10_23)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f134,f218,f123,f225,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X8,X1] : (~sP0(X0,X1,X2) | ~m1_connsp_2(X8,X1,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | r1_waybel_0(X1,X0,X8)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r1_waybel_0(X1,X0,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X1,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X1,X0,X5) | ~m1_connsp_2(X5,X1,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X1,X0,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X1,X6))) & (! [X8] : (r1_waybel_0(X1,X0,X8) | ~m1_connsp_2(X8,X1,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f45,f48,f47,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X1,X0,X4) & m1_connsp_2(X4,X1,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X1,X0,X5) | ~m1_connsp_2(X5,X1,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X1))) => ((? [X4] : (~r1_waybel_0(X1,X0,X4) & m1_connsp_2(X4,X1,sK7(X0,X1,X2))) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X1,X0,X5) | ~m1_connsp_2(X5,X1,sK7(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X1,X0,X4) & m1_connsp_2(X4,X1,sK7(X0,X1,X2))) => (~r1_waybel_0(X1,X0,sK8(X0,X1,X2)) & m1_connsp_2(sK8(X0,X1,X2),X1,sK7(X0,X1,X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X1,X0,X7) & m1_connsp_2(X7,X1,X6)) => (~r1_waybel_0(X1,X0,sK9(X0,X1,X6)) & m1_connsp_2(sK9(X0,X1,X6),X1,X6)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((? [X4] : (~r1_waybel_0(X1,X0,X4) & m1_connsp_2(X4,X1,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X1,X0,X5) | ~m1_connsp_2(X5,X1,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X1,X0,X7) & m1_connsp_2(X7,X1,X6))) & (! [X8] : (r1_waybel_0(X1,X0,X8) | ~m1_connsp_2(X8,X1,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 0.21/0.48    inference(flattening,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3)) | spl10_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    sP0(sK4,sK2,k10_yellow_6(sK2,sK4)) | ~spl10_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f216])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    r2_hidden(sK3,k10_yellow_6(sK2,sK4)) | ~spl10_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~spl10_23 | spl10_1 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_9 | ~spl10_14 | ~spl10_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f186,f182,f155,f127,f116,f111,f106,f101,f86,f223])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl10_4 <=> v2_struct_0(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl10_5 <=> v4_orders_2(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl10_6 <=> v7_waybel_0(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl10_7 <=> l1_waybel_0(sK4,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl10_9 <=> l1_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl10_14 <=> r1_waybel_0(sK2,sK4,sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl10_18 <=> r1_xboole_0(sK5,sK6(sK2,sK5,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~r1_waybel_0(sK2,sK4,sK6(sK2,sK5,sK3)) | (spl10_1 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_9 | ~spl10_14 | ~spl10_18)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f129,f103,f108,f184,f118,f157,f113,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X1) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~r1_xboole_0(X2,X3) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v7_waybel_0(sK4) | ~spl10_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    r1_waybel_0(sK2,sK4,sK5) | ~spl10_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f155])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    l1_waybel_0(sK4,sK2) | ~spl10_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    r1_xboole_0(sK5,sK6(sK2,sK5,sK3)) | ~spl10_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f182])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v4_orders_2(sK4) | ~spl10_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~v2_struct_0(sK4) | spl10_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    l1_struct_0(sK2) | ~spl10_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f127])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    spl10_22 | ~spl10_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f212,f208,f216])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    spl10_21 <=> sP1(k10_yellow_6(sK2,sK4),sK2,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    sP0(sK4,sK2,k10_yellow_6(sK2,sK4)) | ~spl10_21),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f210,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~sP1(k10_yellow_6(X1,X2),X1,X2) | sP0(X2,X1,k10_yellow_6(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k10_yellow_6(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((k10_yellow_6(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k10_yellow_6(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X2,X0,X1] : (((k10_yellow_6(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k10_yellow_6(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X2,X0,X1] : ((k10_yellow_6(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    sP1(k10_yellow_6(sK2,sK4),sK2,sK4) | ~spl10_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f208])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    spl10_21 | spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f192,f163,f116,f111,f106,f101,f96,f91,f86,f208])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl10_15 <=> m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    sP1(k10_yellow_6(sK2,sK4),sK2,sK4) | (spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_15)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f165,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | sP1(X2,X0,X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(definition_folding,[],[f23,f29,f28])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl10_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl10_20 | spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f191,f137,f116,f111,f106,f101,f96,f91,f86,f202])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    spl10_20 <=> sP1(sK5,sK2,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    sP1(sK5,sK2,sK4) | (spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f139,f81])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~spl10_19 | spl10_1 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_9 | ~spl10_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f155,f127,f116,f111,f106,f101,f86,f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl10_19 <=> r1_xboole_0(sK5,sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~r1_xboole_0(sK5,sK5) | (spl10_1 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_9 | ~spl10_14)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f129,f103,f108,f118,f157,f157,f113,f69])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl10_18 | spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f175,f142,f137,f121,f96,f86,f182])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    r1_xboole_0(sK5,sK6(sK2,sK5,sK3)) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X1,sK6(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl10_17 | spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f142,f137,f121,f96,f86,f177])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    r2_hidden(sK3,sK6(sK2,sK5,sK3)) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,sK6(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl10_16 | spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f167,f142,f137,f121,f96,f86,f169])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    v3_pre_topc(sK6(sK2,sK5,sK3),sK2) | (spl10_1 | ~spl10_3 | ~spl10_8 | ~spl10_11 | spl10_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f88,f123,f144,f139,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl10_15 | spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f161,f116,f111,f106,f101,f96,f91,f86,f163])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    m1_subset_1(k10_yellow_6(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | (spl10_1 | ~spl10_2 | ~spl10_3 | spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f93,f98,f103,f108,f113,f118,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl10_14 | spl10_1 | spl10_4 | ~spl10_7 | ~spl10_9 | ~spl10_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f153,f147,f127,f116,f101,f86,f155])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl10_13 <=> k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    r1_waybel_0(sK2,sK4,sK5) | (spl10_1 | spl10_4 | ~spl10_7 | ~spl10_9 | ~spl10_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f151,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5 | ~spl10_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    r1_waybel_0(sK2,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4))) | (spl10_1 | spl10_4 | ~spl10_7 | ~spl10_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f129,f103,f118,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    spl10_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f147])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    (((~r2_hidden(sK3,k2_pre_topc(sK2,sK5)) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK3,k10_yellow_6(sK2,sK4)) & l1_waybel_0(sK4,sK2) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f34,f33,f32,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X1,k10_yellow_6(sK2,X2)) & l1_waybel_0(X2,sK2) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X1,k10_yellow_6(sK2,X2)) & l1_waybel_0(X2,sK2) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (? [X3] : (~r2_hidden(sK3,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK3,k10_yellow_6(sK2,X2)) & l1_waybel_0(X2,sK2) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r2_hidden(sK3,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK2),u1_waybel_0(sK2,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK3,k10_yellow_6(sK2,X2)) & l1_waybel_0(X2,sK2) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(sK3,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK3,k10_yellow_6(sK2,sK4)) & l1_waybel_0(sK4,sK2) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ? [X3] : (~r2_hidden(sK3,k2_pre_topc(sK2,X3)) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~r2_hidden(sK3,k2_pre_topc(sK2,sK5)) & k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK2),u1_waybel_0(sK2,sK4)) = sK5 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_9)).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~spl10_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f142])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_pre_topc(sK2,sK5))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl10_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f59,f137])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl10_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f132])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    r2_hidden(sK3,k10_yellow_6(sK2,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl10_9 | ~spl10_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f125,f96,f127])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    l1_struct_0(sK2) | ~spl10_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl10_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f53,f121])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl10_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f116])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    l1_waybel_0(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl10_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f111])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v7_waybel_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl10_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f55,f106])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v4_orders_2(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~spl10_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f101])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~v2_struct_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl10_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f96])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl10_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f91])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~spl10_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f86])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23429)------------------------------
% 0.21/0.48  % (23429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23429)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23429)Memory used [KB]: 1791
% 0.21/0.48  % (23429)Time elapsed: 0.072 s
% 0.21/0.48  % (23429)------------------------------
% 0.21/0.48  % (23429)------------------------------
% 0.21/0.49  % (23421)Success in time 0.127 s
%------------------------------------------------------------------------------
