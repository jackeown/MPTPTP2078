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
% DateTime   : Thu Dec  3 13:18:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 549 expanded)
%              Number of leaves         :   52 ( 259 expanded)
%              Depth                    :   24
%              Number of atoms          : 1231 (5762 expanded)
%              Number of equality atoms :   39 ( 348 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f198,f204,f225,f243,f249,f269,f282,f308,f329,f340,f385,f441,f542,f543,f547])).

fof(f547,plain,
    ( ~ spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18
    | spl10_19 ),
    inference(subsumption_resolution,[],[f545,f202])).

fof(f202,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl10_19
  <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f545,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | ~ spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f189,f184,f179,f174,f169,f164,f159,f144,f134,f197,f129,f154,f149,f108,f98])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

% (23178)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f108,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_1
  <=> r1_tmap_1(sK3,sK2,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f149,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl10_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f154,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl10_10
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f129,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_5
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f197,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl10_18
  <=> m1_subset_1(sK6,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f134,plain,
    ( m1_pre_topc(sK5,sK3)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_6
  <=> m1_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f144,plain,
    ( ~ v2_struct_0(sK5)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_8
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f159,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_11
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f164,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_12
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f169,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl10_13
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f174,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl10_14
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f179,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl10_15
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f184,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl10_16
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f189,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl10_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f543,plain,
    ( sK6 != sK7
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f542,plain,
    ( spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_36 ),
    inference(avatar_contradiction_clause,[],[f541])).

fof(f541,plain,
    ( $false
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_36 ),
    inference(subsumption_resolution,[],[f540,f418])).

fof(f418,plain,
    ( sP8(sK5,sK3,sK6)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl10_36
  <=> sP8(sK5,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f540,plain,
    ( ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | spl10_17
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f539,f189])).

fof(f539,plain,
    ( v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f538,f184])).

fof(f538,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_15
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f537,f179])).

fof(f537,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f536,f174])).

fof(f536,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f535,f169])).

fof(f535,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f534,f164])).

fof(f534,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f533,f159])).

fof(f533,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f532,f154])).

fof(f532,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f531,f149])).

fof(f531,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | spl10_8
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f530,f144])).

fof(f530,plain,
    ( v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f529,f134])).

fof(f529,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f528,f129])).

fof(f528,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_18
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f527,f197])).

fof(f527,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | spl10_1
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f491,f109])).

fof(f109,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f491,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP8(sK5,sK3,sK6)
    | ~ spl10_19 ),
    inference(resolution,[],[f103,f203])).

fof(f203,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f103,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6)
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
      | ~ sP8(X3,X1,X6) ) ),
    inference(general_splitting,[],[f99,f102_D])).

fof(f102,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP8(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f102_D])).

fof(f102_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP8(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f441,plain,
    ( spl10_36
    | ~ spl10_31
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f398,f382,f305,f416])).

fof(f305,plain,
    ( spl10_31
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f382,plain,
    ( spl10_35
  <=> m1_connsp_2(u1_struct_0(sK5),sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f398,plain,
    ( sP8(sK5,sK3,sK6)
    | ~ spl10_31
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f251,f384,f364])).

% (23181)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f364,plain,
    ( ! [X12,X11] :
        ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,X12)
        | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(X11))
        | sP8(X11,sK3,X12) )
    | ~ spl10_31 ),
    inference(resolution,[],[f102,f307])).

fof(f307,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f305])).

fof(f384,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f382])).

fof(f251,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f191,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f191,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f385,plain,
    ( spl10_35
    | ~ spl10_5
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_28
    | ~ spl10_31
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f373,f335,f305,f266,f172,f167,f162,f127,f382])).

fof(f266,plain,
    ( spl10_28
  <=> r2_hidden(sK6,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f335,plain,
    ( spl10_34
  <=> v3_pre_topc(u1_struct_0(sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f373,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | ~ spl10_5
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_28
    | ~ spl10_31
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f174,f169,f164,f268,f129,f337,f307,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f337,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f335])).

fof(f268,plain,
    ( r2_hidden(sK6,u1_struct_0(sK5))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f266])).

fof(f340,plain,
    ( spl10_34
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f339,f326,f279,f335])).

fof(f279,plain,
    ( spl10_30
  <=> sP0(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f326,plain,
    ( spl10_33
  <=> sP1(sK3,u1_struct_0(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f339,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f333,f281])).

fof(f281,plain,
    ( sP0(sK3,sK5)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f279])).

fof(f333,plain,
    ( ~ sP0(sK3,sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ spl10_33 ),
    inference(resolution,[],[f328,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X0,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f328,plain,
    ( sP1(sK3,u1_struct_0(sK5),sK5)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f329,plain,
    ( spl10_33
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f322,f167,f162,f132,f326])).

fof(f322,plain,
    ( sP1(sK3,u1_struct_0(sK5),sK5)
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f169,f164,f134,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f101,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f34,f42,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f308,plain,
    ( spl10_31
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f301,f162,f132,f305])).

fof(f301,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f164,f134,f80])).

fof(f282,plain,
    ( spl10_30
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f275,f137,f132,f279])).

fof(f137,plain,
    ( spl10_7
  <=> v1_tsep_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f275,plain,
    ( sP0(sK3,sK5)
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f139,f134,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f139,plain,
    ( v1_tsep_1(sK5,sK3)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f269,plain,
    ( spl10_28
    | ~ spl10_18
    | spl10_26 ),
    inference(avatar_split_clause,[],[f264,f246,f195,f266])).

fof(f246,plain,
    ( spl10_26
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f264,plain,
    ( r2_hidden(sK6,u1_struct_0(sK5))
    | ~ spl10_18
    | spl10_26 ),
    inference(unit_resulting_resolution,[],[f197,f248,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f248,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | spl10_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f249,plain,
    ( ~ spl10_26
    | spl10_8
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f244,f240,f142,f246])).

fof(f240,plain,
    ( spl10_25
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f244,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | spl10_8
    | ~ spl10_25 ),
    inference(unit_resulting_resolution,[],[f144,f242,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f242,plain,
    ( l1_struct_0(sK5)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f243,plain,
    ( spl10_25
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f238,f220,f240])).

fof(f220,plain,
    ( spl10_22
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f238,plain,
    ( l1_struct_0(sK5)
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f222,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f222,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f225,plain,
    ( spl10_22
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f224,f162,f132,f220])).

fof(f224,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f218,f164])).

fof(f218,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f79,f134])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f204,plain,
    ( spl10_19
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f199,f117,f111,f201])).

fof(f111,plain,
    ( spl10_2
  <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f117,plain,
    ( spl10_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f199,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f112,f119])).

fof(f119,plain,
    ( sK6 = sK7
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f112,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f198,plain,
    ( spl10_18
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f193,f122,f117,f195])).

fof(f122,plain,
    ( spl10_4
  <=> m1_subset_1(sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f193,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f124,f119])).

fof(f124,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f190,plain,(
    ~ spl10_17 ),
    inference(avatar_split_clause,[],[f59,f187])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | r1_tmap_1(sK3,sK2,sK4,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_pre_topc(sK5,sK3)
    & v1_tsep_1(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f45,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK2,X2,X4) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | r1_tmap_1(X1,sK2,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK2,X2,X4) )
                        & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                          | r1_tmap_1(X1,sK2,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5)
                        | ~ r1_tmap_1(sK3,sK2,X2,X4) )
                      & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5)
                        | r1_tmap_1(sK3,sK2,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK3)) )
              & m1_pre_topc(X3,sK3)
              & v1_tsep_1(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5)
                      | ~ r1_tmap_1(sK3,sK2,X2,X4) )
                    & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5)
                      | r1_tmap_1(sK3,sK2,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK3)) )
            & m1_pre_topc(X3,sK3)
            & v1_tsep_1(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5)
                    | ~ r1_tmap_1(sK3,sK2,sK4,X4) )
                  & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5)
                    | r1_tmap_1(sK3,sK2,sK4,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK3)) )
          & m1_pre_topc(X3,sK3)
          & v1_tsep_1(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5)
                  | ~ r1_tmap_1(sK3,sK2,sK4,X4) )
                & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5)
                  | r1_tmap_1(sK3,sK2,sK4,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK3)) )
        & m1_pre_topc(X3,sK3)
        & v1_tsep_1(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
                | ~ r1_tmap_1(sK3,sK2,sK4,X4) )
              & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
                | r1_tmap_1(sK3,sK2,sK4,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_subset_1(X4,u1_struct_0(sK3)) )
      & m1_pre_topc(sK5,sK3)
      & v1_tsep_1(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
              | ~ r1_tmap_1(sK3,sK2,sK4,X4) )
            & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
              | r1_tmap_1(sK3,sK2,sK4,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_subset_1(X4,u1_struct_0(sK3)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
            | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
          & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
            | r1_tmap_1(sK3,sK2,sK4,sK6) )
          & sK6 = X5
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
          | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
        & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5)
          | r1_tmap_1(sK3,sK2,sK4,sK6) )
        & sK6 = X5
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
        | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
      & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
        | r1_tmap_1(sK3,sK2,sK4,sK6) )
      & sK6 = sK7
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f185,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f60,f182])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f180,plain,(
    spl10_15 ),
    inference(avatar_split_clause,[],[f61,f177])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f175,plain,(
    ~ spl10_14 ),
    inference(avatar_split_clause,[],[f62,f172])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f170,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f63,f167])).

fof(f63,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f165,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f64,f162])).

fof(f64,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f160,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f65,f157])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f155,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f66,f152])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f150,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f67,f147])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f145,plain,(
    ~ spl10_8 ),
    inference(avatar_split_clause,[],[f68,f142])).

fof(f68,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f140,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f69,f137])).

fof(f69,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f135,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f70,f132])).

fof(f70,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f71,f127])).

fof(f71,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f72,f122])).

fof(f72,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f73,f117])).

fof(f73,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f74,f111,f107])).

fof(f74,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f75,f111,f107])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (23179)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.43  % (23187)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.44  % (23187)Refutation not found, incomplete strategy% (23187)------------------------------
% 0.20/0.44  % (23187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23187)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (23187)Memory used [KB]: 1663
% 0.20/0.44  % (23187)Time elapsed: 0.055 s
% 0.20/0.44  % (23187)------------------------------
% 0.20/0.44  % (23187)------------------------------
% 0.20/0.46  % (23175)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (23192)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (23190)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (23175)Refutation not found, incomplete strategy% (23175)------------------------------
% 0.20/0.48  % (23175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23175)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23175)Memory used [KB]: 10618
% 0.20/0.48  % (23175)Time elapsed: 0.067 s
% 0.20/0.48  % (23175)------------------------------
% 0.20/0.48  % (23175)------------------------------
% 0.20/0.48  % (23180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (23190)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f548,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f114,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f198,f204,f225,f243,f249,f269,f282,f308,f329,f340,f385,f441,f542,f543,f547])).
% 0.20/0.49  fof(f547,plain,(
% 0.20/0.49    ~spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18 | spl10_19),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f546])).
% 0.20/0.49  fof(f546,plain,(
% 0.20/0.49    $false | (~spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18 | spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f545,f202])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) | spl10_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    spl10_19 <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.49  fof(f545,plain,(
% 0.20/0.49    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) | (~spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f189,f184,f179,f174,f169,f164,f159,f144,f134,f197,f129,f154,f149,f108,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  % (23178)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK2,sK4,sK6) | ~spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl10_1 <=> r1_tmap_1(sK3,sK2,sK4,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~spl10_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl10_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl10_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl10_10 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl10_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    spl10_5 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK5)) | ~spl10_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl10_18 <=> m1_subset_1(sK6,u1_struct_0(sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    m1_pre_topc(sK5,sK3) | ~spl10_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl10_6 <=> m1_pre_topc(sK5,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~v2_struct_0(sK5) | spl10_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl10_8 <=> v2_struct_0(sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    v1_funct_1(sK4) | ~spl10_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl10_11 <=> v1_funct_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    l1_pre_topc(sK3) | ~spl10_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    spl10_12 <=> l1_pre_topc(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    v2_pre_topc(sK3) | ~spl10_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl10_13 <=> v2_pre_topc(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~v2_struct_0(sK3) | spl10_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f172])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    spl10_14 <=> v2_struct_0(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    l1_pre_topc(sK2) | ~spl10_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    spl10_15 <=> l1_pre_topc(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    v2_pre_topc(sK2) | ~spl10_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl10_16 <=> v2_pre_topc(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~v2_struct_0(sK2) | spl10_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f187])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    spl10_17 <=> v2_struct_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.49  fof(f543,plain,(
% 0.20/0.49    sK6 != sK7 | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18 | ~spl10_19 | ~spl10_36),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f541])).
% 0.20/0.49  fof(f541,plain,(
% 0.20/0.49    $false | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18 | ~spl10_19 | ~spl10_36)),
% 0.20/0.49    inference(subsumption_resolution,[],[f540,f418])).
% 0.20/0.49  fof(f418,plain,(
% 0.20/0.49    sP8(sK5,sK3,sK6) | ~spl10_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f416])).
% 0.20/0.49  fof(f416,plain,(
% 0.20/0.49    spl10_36 <=> sP8(sK5,sK3,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.20/0.49  fof(f540,plain,(
% 0.20/0.49    ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | spl10_17 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f539,f189])).
% 0.20/0.49  fof(f539,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f538,f184])).
% 0.20/0.49  fof(f538,plain,(
% 0.20/0.49    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_15 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f537,f179])).
% 0.20/0.49  fof(f537,plain,(
% 0.20/0.49    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f536,f174])).
% 0.20/0.49  fof(f536,plain,(
% 0.20/0.49    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_13 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f535,f169])).
% 0.20/0.49  fof(f535,plain,(
% 0.20/0.49    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_12 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f534,f164])).
% 0.20/0.49  fof(f534,plain,(
% 0.20/0.49    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f533,f159])).
% 0.20/0.49  fof(f533,plain,(
% 0.20/0.49    ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f532,f154])).
% 0.20/0.49  fof(f532,plain,(
% 0.20/0.49    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_9 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f531,f149])).
% 0.20/0.49  fof(f531,plain,(
% 0.20/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | spl10_8 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f530,f144])).
% 0.20/0.49  fof(f530,plain,(
% 0.20/0.49    v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f529,f134])).
% 0.20/0.49  fof(f529,plain,(
% 0.20/0.49    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_5 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f528,f129])).
% 0.20/0.49  fof(f528,plain,(
% 0.20/0.49    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_18 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f527,f197])).
% 0.20/0.49  fof(f527,plain,(
% 0.20/0.49    ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | (spl10_1 | ~spl10_19)),
% 0.20/0.49    inference(subsumption_resolution,[],[f491,f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK2,sK4,sK6) | spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f107])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK2,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP8(sK5,sK3,sK6) | ~spl10_19),
% 0.20/0.49    inference(resolution,[],[f103,f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) | ~spl10_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f201])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X6,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP8(X3,X1,X6)) )),
% 0.20/0.49    inference(general_splitting,[],[f99,f102_D])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP8(X3,X1,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f102_D])).
% 0.20/0.49  fof(f102_D,plain,(
% 0.20/0.49    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP8(X3,X1,X6)) )),
% 0.20/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.49  fof(f441,plain,(
% 0.20/0.49    spl10_36 | ~spl10_31 | ~spl10_35),
% 0.20/0.49    inference(avatar_split_clause,[],[f398,f382,f305,f416])).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    spl10_31 <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.20/0.49  fof(f382,plain,(
% 0.20/0.49    spl10_35 <=> m1_connsp_2(u1_struct_0(sK5),sK3,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 0.20/0.49  fof(f398,plain,(
% 0.20/0.49    sP8(sK5,sK3,sK6) | (~spl10_31 | ~spl10_35)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f251,f384,f364])).
% 0.20/0.49  % (23181)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  fof(f364,plain,(
% 0.20/0.49    ( ! [X12,X11] : (~m1_connsp_2(u1_struct_0(sK5),sK3,X12) | ~r1_tarski(u1_struct_0(sK5),u1_struct_0(X11)) | sP8(X11,sK3,X12)) ) | ~spl10_31),
% 0.20/0.49    inference(resolution,[],[f102,f307])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl10_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f305])).
% 0.20/0.49  fof(f384,plain,(
% 0.20/0.49    m1_connsp_2(u1_struct_0(sK5),sK3,sK6) | ~spl10_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f382])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f191,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f77,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    spl10_35 | ~spl10_5 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_28 | ~spl10_31 | ~spl10_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f373,f335,f305,f266,f172,f167,f162,f127,f382])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    spl10_28 <=> r2_hidden(sK6,u1_struct_0(sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    spl10_34 <=> v3_pre_topc(u1_struct_0(sK5),sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 0.20/0.49  fof(f373,plain,(
% 0.20/0.49    m1_connsp_2(u1_struct_0(sK5),sK3,sK6) | (~spl10_5 | ~spl10_12 | ~spl10_13 | spl10_14 | ~spl10_28 | ~spl10_31 | ~spl10_34)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f174,f169,f164,f268,f129,f337,f307,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    v3_pre_topc(u1_struct_0(sK5),sK3) | ~spl10_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f335])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    r2_hidden(sK6,u1_struct_0(sK5)) | ~spl10_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f266])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    spl10_34 | ~spl10_30 | ~spl10_33),
% 0.20/0.49    inference(avatar_split_clause,[],[f339,f326,f279,f335])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    spl10_30 <=> sP0(sK3,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.20/0.49  fof(f326,plain,(
% 0.20/0.49    spl10_33 <=> sP1(sK3,u1_struct_0(sK5),sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    v3_pre_topc(u1_struct_0(sK5),sK3) | (~spl10_30 | ~spl10_33)),
% 0.20/0.49    inference(subsumption_resolution,[],[f333,f281])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    sP0(sK3,sK5) | ~spl10_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f279])).
% 0.20/0.49  fof(f333,plain,(
% 0.20/0.49    ~sP0(sK3,sK5) | v3_pre_topc(u1_struct_0(sK5),sK3) | ~spl10_33),
% 0.20/0.49    inference(resolution,[],[f328,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X0,X2) | v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    sP1(sK3,u1_struct_0(sK5),sK5) | ~spl10_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f326])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    spl10_33 | ~spl10_6 | ~spl10_12 | ~spl10_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f322,f167,f162,f132,f326])).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    sP1(sK3,u1_struct_0(sK5),sK5) | (~spl10_6 | ~spl10_12 | ~spl10_13)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f169,f164,f134,f192])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f34,f42,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    spl10_31 | ~spl10_6 | ~spl10_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f301,f162,f132,f305])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl10_6 | ~spl10_12)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f164,f134,f80])).
% 0.20/0.49  fof(f282,plain,(
% 0.20/0.49    spl10_30 | ~spl10_6 | ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f275,f137,f132,f279])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl10_7 <=> v1_tsep_1(sK5,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    sP0(sK3,sK5) | (~spl10_6 | ~spl10_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f139,f134,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f41])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    v1_tsep_1(sK5,sK3) | ~spl10_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl10_28 | ~spl10_18 | spl10_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f264,f246,f195,f266])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    spl10_26 <=> v1_xboole_0(u1_struct_0(sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    r2_hidden(sK6,u1_struct_0(sK5)) | (~spl10_18 | spl10_26)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f197,f248,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ~v1_xboole_0(u1_struct_0(sK5)) | spl10_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f246])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    ~spl10_26 | spl10_8 | ~spl10_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f244,f240,f142,f246])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl10_25 <=> l1_struct_0(sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ~v1_xboole_0(u1_struct_0(sK5)) | (spl10_8 | ~spl10_25)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f144,f242,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    l1_struct_0(sK5) | ~spl10_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f240])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    spl10_25 | ~spl10_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f238,f220,f240])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    spl10_22 <=> l1_pre_topc(sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    l1_struct_0(sK5) | ~spl10_22),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f222,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    l1_pre_topc(sK5) | ~spl10_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f220])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    spl10_22 | ~spl10_6 | ~spl10_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f162,f132,f220])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    l1_pre_topc(sK5) | (~spl10_6 | ~spl10_12)),
% 0.20/0.49    inference(subsumption_resolution,[],[f218,f164])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    l1_pre_topc(sK5) | ~l1_pre_topc(sK3) | ~spl10_6),
% 0.20/0.49    inference(resolution,[],[f79,f134])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    spl10_19 | ~spl10_2 | ~spl10_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f199,f117,f111,f201])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl10_2 <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl10_3 <=> sK6 = sK7),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) | (~spl10_2 | ~spl10_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f112,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    sK6 = sK7 | ~spl10_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~spl10_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    spl10_18 | ~spl10_3 | ~spl10_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f193,f122,f117,f195])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl10_4 <=> m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK5)) | (~spl10_3 | ~spl10_4)),
% 0.20/0.49    inference(backward_demodulation,[],[f124,f119])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    m1_subset_1(sK7,u1_struct_0(sK5)) | ~spl10_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f122])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ~spl10_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f59,f187])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f45,f51,f50,f49,f48,f47,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5) | ~r1_tmap_1(sK3,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5) | r1_tmap_1(sK3,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5) | ~r1_tmap_1(sK3,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X5) | r1_tmap_1(sK3,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5) | ~r1_tmap_1(sK3,sK2,sK4,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5) | r1_tmap_1(sK3,sK2,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5) | ~r1_tmap_1(sK3,sK2,sK4,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X5) | r1_tmap_1(sK3,sK2,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | ~r1_tmap_1(sK3,sK2,sK4,X4)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | r1_tmap_1(sK3,sK2,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ? [X4] : (? [X5] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | ~r1_tmap_1(sK3,sK2,sK4,X4)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | r1_tmap_1(sK3,sK2,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK3))) => (? [X5] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ? [X5] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X5) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) => ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f16])).
% 0.20/0.49  fof(f16,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl10_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f182])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    v2_pre_topc(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    spl10_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f177])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    l1_pre_topc(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~spl10_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f62,f172])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    spl10_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f63,f167])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v2_pre_topc(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl10_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f162])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    l1_pre_topc(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl10_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f157])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    v1_funct_1(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl10_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f152])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl10_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f147])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~spl10_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f142])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~v2_struct_0(sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f69,f137])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    v1_tsep_1(sK5,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl10_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f132])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    m1_pre_topc(sK5,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl10_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f71,f127])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl10_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f122])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl10_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f73,f117])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    sK6 = sK7),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl10_1 | spl10_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f74,f111,f107])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~spl10_1 | ~spl10_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f75,f111,f107])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23190)------------------------------
% 0.20/0.49  % (23190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23190)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23190)Memory used [KB]: 11129
% 0.20/0.49  % (23190)Time elapsed: 0.077 s
% 0.20/0.49  % (23190)------------------------------
% 0.20/0.49  % (23190)------------------------------
% 0.20/0.49  % (23170)Success in time 0.138 s
%------------------------------------------------------------------------------
