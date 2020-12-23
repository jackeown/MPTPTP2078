%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 624 expanded)
%              Number of leaves         :   50 ( 310 expanded)
%              Depth                    :   14
%              Number of atoms          : 1182 (8229 expanded)
%              Number of equality atoms :   45 ( 470 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f197,f223,f229,f235,f255,f260,f270,f300,f355,f371,f433,f438,f447,f451])).

fof(f451,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20
    | spl7_21 ),
    inference(subsumption_resolution,[],[f449,f448])).

fof(f448,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_14
    | spl7_21 ),
    inference(forward_demodulation,[],[f221,f174])).

fof(f174,plain,
    ( sK5 = sK6
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_14
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f221,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl7_21
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f449,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f109,f114,f119,f124,f129,f134,f144,f139,f159,f154,f149,f169,f184,f179,f189,f196,f218,f94])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f218,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_20
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f196,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f189,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_17
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f179,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_15
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f184,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_16
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f169,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f149,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f154,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f159,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f139,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f144,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f134,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f129,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f124,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f119,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f114,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f109,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f447,plain,
    ( spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_44
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_25
    | ~ spl7_27
    | ~ spl7_44
    | spl7_45 ),
    inference(subsumption_resolution,[],[f439,f432])).

fof(f432,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl7_44
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f439,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | spl7_8
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_25
    | ~ spl7_27
    | spl7_45 ),
    inference(unit_resulting_resolution,[],[f269,f259,f144,f164,f169,f437,f333])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | m1_connsp_2(u1_struct_0(X1),X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ v1_tsep_1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | m1_connsp_2(u1_struct_0(X1),X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ v1_tsep_1(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f250,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f100,f76])).

% (4646)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (4627)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f76,plain,(
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

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f34])).

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

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X2)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | m1_connsp_2(u1_struct_0(X1),X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X2) ) ),
    inference(subsumption_resolution,[],[f249,f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f76,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v3_pre_topc(u1_struct_0(X1),X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | m1_connsp_2(u1_struct_0(X1),X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v3_pre_topc(u1_struct_0(X1),X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | m1_connsp_2(u1_struct_0(X1),X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f78,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f437,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK2),sK3,sK5)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl7_45
  <=> m1_connsp_2(u1_struct_0(sK2),sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f164,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_12
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f259,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl7_25
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f269,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_27
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f438,plain,
    ( ~ spl7_45
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_20
    | ~ spl7_22
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f379,f368,f226,f216,f194,f187,f182,f177,f167,f157,f147,f142,f137,f132,f127,f122,f117,f112,f107,f435])).

fof(f226,plain,
    ( spl7_22
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f368,plain,
    ( spl7_36
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f379,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK2),sK3,sK5)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | spl7_8
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_20
    | ~ spl7_22
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f109,f114,f119,f124,f129,f134,f139,f144,f149,f159,f169,f184,f179,f98,f217,f189,f228,f196,f370,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
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
    inference(subsumption_resolution,[],[f92,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f92,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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

fof(f370,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f368])).

fof(f228,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f226])).

fof(f217,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f433,plain,
    ( spl7_44
    | ~ spl7_16
    | spl7_35 ),
    inference(avatar_split_clause,[],[f405,f352,f182,f430])).

fof(f352,plain,
    ( spl7_35
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f405,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl7_16
    | spl7_35 ),
    inference(unit_resulting_resolution,[],[f184,f354,f87])).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f354,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_35 ),
    inference(avatar_component_clause,[],[f352])).

fof(f371,plain,
    ( spl7_36
    | ~ spl7_13
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f280,f257,f167,f368])).

fof(f280,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl7_13
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f169,f259,f76])).

fof(f355,plain,
    ( ~ spl7_35
    | spl7_7
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f334,f297,f137,f352])).

fof(f297,plain,
    ( spl7_28
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f334,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_7
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f139,f299,f77])).

fof(f77,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f299,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f297])).

fof(f300,plain,
    ( spl7_28
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f272,f252,f297])).

fof(f252,plain,
    ( spl7_24
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f272,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f254,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f254,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f270,plain,
    ( spl7_27
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f208,f157,f117,f112,f267])).

fof(f208,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f114,f159,f119,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f260,plain,
    ( spl7_25
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f204,f157,f117,f257])).

fof(f204,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f159,f119,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f255,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f203,f152,f117,f252])).

fof(f203,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f154,f119,f75])).

fof(f235,plain,
    ( ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f73,f220,f216])).

fof(f73,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f47,f46,f45,f44,f43,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f229,plain,
    ( spl7_22
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f224,f220,f172,f226])).

fof(f224,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f222,f174])).

fof(f222,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( spl7_20
    | spl7_21 ),
    inference(avatar_split_clause,[],[f72,f220,f216])).

fof(f72,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f197,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f66,f194])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f190,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f65,f187])).

fof(f65,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f185,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f101,f182])).

fof(f101,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f70,f71])).

fof(f71,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f180,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f69,f177])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f175,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f71,f172])).

fof(f170,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f68,f167])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f165,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f67,f162])).

fof(f67,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f160,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f63,f157])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f155,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f61,f152])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f150,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f64,f147])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f145,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f62,f142])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f140,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f60,f137])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f135,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f59,f132])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f130,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f125,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (4641)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (4631)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (4643)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (4635)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (4649)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (4640)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (4631)Refutation not found, incomplete strategy% (4631)------------------------------
% 0.22/0.54  % (4631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4631)Memory used [KB]: 6140
% 0.22/0.54  % (4631)Time elapsed: 0.087 s
% 0.22/0.54  % (4631)------------------------------
% 0.22/0.54  % (4631)------------------------------
% 0.22/0.55  % (4632)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (4649)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f452,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f197,f223,f229,f235,f255,f260,f270,f300,f355,f371,f433,f438,f447,f451])).
% 0.22/0.56  fof(f451,plain,(
% 0.22/0.56    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_20 | spl7_21),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f450])).
% 0.22/0.56  fof(f450,plain,(
% 0.22/0.56    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_13 | ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_20 | spl7_21)),
% 0.22/0.56    inference(subsumption_resolution,[],[f449,f448])).
% 0.22/0.56  fof(f448,plain,(
% 0.22/0.56    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl7_14 | spl7_21)),
% 0.22/0.56    inference(forward_demodulation,[],[f221,f174])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    sK5 = sK6 | ~spl7_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f172])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    spl7_14 <=> sK5 = sK6),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | spl7_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f220])).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    spl7_21 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.56  fof(f449,plain,(
% 0.22/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_13 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_20)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f109,f114,f119,f124,f129,f134,f144,f139,f159,f154,f149,f169,f184,f179,f189,f196,f218,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl7_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f216])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    spl7_20 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f194])).
% 0.22/0.56  fof(f194,plain,(
% 0.22/0.56    spl7_18 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.56  fof(f189,plain,(
% 0.22/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f187])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    spl7_17 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl7_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f177])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    spl7_15 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f182])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    spl7_16 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.56  fof(f169,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK3) | ~spl7_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f167])).
% 0.22/0.56  fof(f167,plain,(
% 0.22/0.56    spl7_13 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    v1_funct_1(sK4) | ~spl7_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f147])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    spl7_9 <=> v1_funct_1(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    m1_pre_topc(sK2,sK0) | ~spl7_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f152])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    spl7_10 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK0) | ~spl7_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f157])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    spl7_11 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    ~v2_struct_0(sK2) | spl7_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f137])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    spl7_7 <=> v2_struct_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ~v2_struct_0(sK3) | spl7_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    spl7_8 <=> v2_struct_0(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    l1_pre_topc(sK1) | ~spl7_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f132])).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    spl7_6 <=> l1_pre_topc(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    v2_pre_topc(sK1) | ~spl7_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    spl7_5 <=> v2_pre_topc(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    ~v2_struct_0(sK1) | spl7_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    spl7_4 <=> v2_struct_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    l1_pre_topc(sK0) | ~spl7_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    spl7_3 <=> l1_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    v2_pre_topc(sK0) | ~spl7_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f112])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    spl7_2 <=> v2_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ~v2_struct_0(sK0) | spl7_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    spl7_1 <=> v2_struct_0(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.56  fof(f447,plain,(
% 0.22/0.56    spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_25 | ~spl7_27 | ~spl7_44 | spl7_45),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f446])).
% 0.22/0.56  fof(f446,plain,(
% 0.22/0.56    $false | (spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_25 | ~spl7_27 | ~spl7_44 | spl7_45)),
% 0.22/0.56    inference(subsumption_resolution,[],[f439,f432])).
% 0.22/0.56  fof(f432,plain,(
% 0.22/0.56    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl7_44),
% 0.22/0.56    inference(avatar_component_clause,[],[f430])).
% 0.22/0.56  fof(f430,plain,(
% 0.22/0.56    spl7_44 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.56  fof(f439,plain,(
% 0.22/0.56    ~r2_hidden(sK5,u1_struct_0(sK2)) | (spl7_8 | ~spl7_12 | ~spl7_13 | ~spl7_25 | ~spl7_27 | spl7_45)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f269,f259,f144,f164,f169,f437,f333])).
% 0.22/0.56  fof(f333,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | m1_connsp_2(u1_struct_0(X1),X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,X2) | ~v1_tsep_1(X1,X2)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f332])).
% 0.22/0.56  fof(f332,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | m1_connsp_2(u1_struct_0(X1),X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X1,X2) | ~v1_tsep_1(X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.22/0.56    inference(resolution,[],[f250,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f100,f76])).
% 1.58/0.58  % (4646)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.58/0.58  % (4627)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.58/0.58  fof(f76,plain,(
% 1.58/0.58    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f20])).
% 1.58/0.58  fof(f20,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f10])).
% 1.58/0.58  fof(f10,axiom,(
% 1.58/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.58/0.58  fof(f100,plain,(
% 1.58/0.58    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f97])).
% 1.58/0.58  fof(f97,plain,(
% 1.58/0.58    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(equality_resolution,[],[f84])).
% 1.58/0.58  fof(f84,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f51])).
% 1.58/0.58  fof(f51,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.58    inference(flattening,[],[f50])).
% 1.58/0.58  fof(f50,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.58    inference(nnf_transformation,[],[f34])).
% 1.58/0.58  fof(f34,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.58    inference(flattening,[],[f33])).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f9])).
% 1.58/0.58  fof(f9,axiom,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.58/0.58  fof(f250,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X2) | ~r2_hidden(X0,u1_struct_0(X1)) | m1_connsp_2(u1_struct_0(X1),X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,X2)) )),
% 1.58/0.58    inference(subsumption_resolution,[],[f249,f239])).
% 1.58/0.58  fof(f239,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | ~l1_pre_topc(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X0,X1)) )),
% 1.58/0.58    inference(resolution,[],[f76,f91])).
% 1.58/0.58  fof(f91,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f38])).
% 1.58/0.58  fof(f38,plain,(
% 1.58/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.58/0.58    inference(flattening,[],[f37])).
% 1.58/0.58  fof(f37,plain,(
% 1.58/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.58/0.58    inference(ennf_transformation,[],[f3])).
% 1.58/0.58  fof(f3,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.58/0.58  fof(f249,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~v3_pre_topc(u1_struct_0(X1),X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | m1_connsp_2(u1_struct_0(X1),X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,X2)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f248])).
% 1.58/0.58  fof(f248,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~v3_pre_topc(u1_struct_0(X1),X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | m1_connsp_2(u1_struct_0(X1),X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X1,X2) | ~l1_pre_topc(X2)) )),
% 1.58/0.58    inference(resolution,[],[f78,f76])).
% 1.58/0.58  fof(f78,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f24])).
% 1.58/0.58  fof(f24,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.58    inference(flattening,[],[f23])).
% 1.58/0.58  fof(f23,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,axiom,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.58/0.58  fof(f437,plain,(
% 1.58/0.58    ~m1_connsp_2(u1_struct_0(sK2),sK3,sK5) | spl7_45),
% 1.58/0.58    inference(avatar_component_clause,[],[f435])).
% 1.58/0.58  fof(f435,plain,(
% 1.58/0.58    spl7_45 <=> m1_connsp_2(u1_struct_0(sK2),sK3,sK5)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.58/0.58  fof(f164,plain,(
% 1.58/0.58    v1_tsep_1(sK2,sK3) | ~spl7_12),
% 1.58/0.58    inference(avatar_component_clause,[],[f162])).
% 1.58/0.58  fof(f162,plain,(
% 1.58/0.58    spl7_12 <=> v1_tsep_1(sK2,sK3)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.58/0.58  fof(f259,plain,(
% 1.58/0.58    l1_pre_topc(sK3) | ~spl7_25),
% 1.58/0.58    inference(avatar_component_clause,[],[f257])).
% 1.58/0.58  fof(f257,plain,(
% 1.58/0.58    spl7_25 <=> l1_pre_topc(sK3)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.58/0.58  fof(f269,plain,(
% 1.58/0.58    v2_pre_topc(sK3) | ~spl7_27),
% 1.58/0.58    inference(avatar_component_clause,[],[f267])).
% 1.58/0.58  fof(f267,plain,(
% 1.58/0.58    spl7_27 <=> v2_pre_topc(sK3)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.58/0.58  fof(f438,plain,(
% 1.58/0.58    ~spl7_45 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_13 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_20 | ~spl7_22 | ~spl7_36),
% 1.58/0.58    inference(avatar_split_clause,[],[f379,f368,f226,f216,f194,f187,f182,f177,f167,f157,f147,f142,f137,f132,f127,f122,f117,f112,f107,f435])).
% 1.58/0.58  fof(f226,plain,(
% 1.58/0.58    spl7_22 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.58/0.58  fof(f368,plain,(
% 1.58/0.58    spl7_36 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 1.58/0.58  fof(f379,plain,(
% 1.58/0.58    ~m1_connsp_2(u1_struct_0(sK2),sK3,sK5) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7 | spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_13 | ~spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_18 | spl7_20 | ~spl7_22 | ~spl7_36)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f109,f114,f119,f124,f129,f134,f139,f144,f149,f159,f169,f184,f179,f98,f217,f189,f228,f196,f370,f102])).
% 1.58/0.58  fof(f102,plain,(
% 1.58/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~m1_connsp_2(X5,X3,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.58    inference(subsumption_resolution,[],[f92,f83])).
% 1.58/0.58  fof(f83,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f32])).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.58    inference(flattening,[],[f31])).
% 1.58/0.58  fof(f31,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f11])).
% 1.58/0.58  fof(f11,axiom,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.58/0.58  fof(f92,plain,(
% 1.58/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.58    inference(equality_resolution,[],[f80])).
% 1.58/0.58  fof(f80,plain,(
% 1.58/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f49])).
% 1.58/0.58  fof(f49,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.58    inference(nnf_transformation,[],[f26])).
% 1.58/0.58  fof(f26,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.58    inference(flattening,[],[f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f13])).
% 1.58/0.58  fof(f13,axiom,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 1.58/0.58  fof(f370,plain,(
% 1.58/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl7_36),
% 1.58/0.58    inference(avatar_component_clause,[],[f368])).
% 1.58/0.58  fof(f228,plain,(
% 1.58/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_22),
% 1.58/0.58    inference(avatar_component_clause,[],[f226])).
% 1.58/0.58  fof(f217,plain,(
% 1.58/0.58    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_20),
% 1.58/0.58    inference(avatar_component_clause,[],[f216])).
% 1.58/0.58  fof(f98,plain,(
% 1.58/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.58    inference(equality_resolution,[],[f89])).
% 1.58/0.58  fof(f89,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f53])).
% 1.58/0.58  fof(f53,plain,(
% 1.58/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.58    inference(flattening,[],[f52])).
% 1.58/0.58  fof(f52,plain,(
% 1.58/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.58  fof(f433,plain,(
% 1.58/0.58    spl7_44 | ~spl7_16 | spl7_35),
% 1.58/0.58    inference(avatar_split_clause,[],[f405,f352,f182,f430])).
% 1.58/0.58  fof(f352,plain,(
% 1.58/0.58    spl7_35 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.58/0.58  fof(f405,plain,(
% 1.58/0.58    r2_hidden(sK5,u1_struct_0(sK2)) | (~spl7_16 | spl7_35)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f184,f354,f87])).
% 1.58/0.58  fof(f87,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f36])).
% 1.58/0.58  fof(f36,plain,(
% 1.58/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.58/0.58    inference(flattening,[],[f35])).
% 1.58/0.58  fof(f35,plain,(
% 1.58/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f2])).
% 1.58/0.58  fof(f2,axiom,(
% 1.58/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.58/0.58  fof(f354,plain,(
% 1.58/0.58    ~v1_xboole_0(u1_struct_0(sK2)) | spl7_35),
% 1.58/0.58    inference(avatar_component_clause,[],[f352])).
% 1.58/0.58  fof(f371,plain,(
% 1.58/0.58    spl7_36 | ~spl7_13 | ~spl7_25),
% 1.58/0.58    inference(avatar_split_clause,[],[f280,f257,f167,f368])).
% 1.58/0.58  fof(f280,plain,(
% 1.58/0.58    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | (~spl7_13 | ~spl7_25)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f169,f259,f76])).
% 1.58/0.58  fof(f355,plain,(
% 1.58/0.58    ~spl7_35 | spl7_7 | ~spl7_28),
% 1.58/0.58    inference(avatar_split_clause,[],[f334,f297,f137,f352])).
% 1.58/0.58  fof(f297,plain,(
% 1.58/0.58    spl7_28 <=> l1_struct_0(sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.58/0.58  fof(f334,plain,(
% 1.58/0.58    ~v1_xboole_0(u1_struct_0(sK2)) | (spl7_7 | ~spl7_28)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f139,f299,f77])).
% 1.58/0.58  fof(f77,plain,(
% 1.58/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f22])).
% 1.58/0.58  fof(f22,plain,(
% 1.58/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.58/0.58    inference(flattening,[],[f21])).
% 1.58/0.58  fof(f21,plain,(
% 1.58/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f7])).
% 1.58/0.58  fof(f7,axiom,(
% 1.58/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.58/0.58  fof(f299,plain,(
% 1.58/0.58    l1_struct_0(sK2) | ~spl7_28),
% 1.58/0.58    inference(avatar_component_clause,[],[f297])).
% 1.58/0.58  fof(f300,plain,(
% 1.58/0.58    spl7_28 | ~spl7_24),
% 1.58/0.58    inference(avatar_split_clause,[],[f272,f252,f297])).
% 1.58/0.58  fof(f252,plain,(
% 1.58/0.58    spl7_24 <=> l1_pre_topc(sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.58/0.58  fof(f272,plain,(
% 1.58/0.58    l1_struct_0(sK2) | ~spl7_24),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f254,f74])).
% 1.58/0.58  fof(f74,plain,(
% 1.58/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f18])).
% 1.58/0.58  fof(f18,plain,(
% 1.58/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f5])).
% 1.58/0.58  fof(f5,axiom,(
% 1.58/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.58/0.58  fof(f254,plain,(
% 1.58/0.58    l1_pre_topc(sK2) | ~spl7_24),
% 1.58/0.58    inference(avatar_component_clause,[],[f252])).
% 1.58/0.58  fof(f270,plain,(
% 1.58/0.58    spl7_27 | ~spl7_2 | ~spl7_3 | ~spl7_11),
% 1.58/0.58    inference(avatar_split_clause,[],[f208,f157,f117,f112,f267])).
% 1.58/0.58  fof(f208,plain,(
% 1.58/0.58    v2_pre_topc(sK3) | (~spl7_2 | ~spl7_3 | ~spl7_11)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f114,f159,f119,f82])).
% 1.58/0.58  fof(f82,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f30])).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.58    inference(flattening,[],[f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f4])).
% 1.58/0.58  fof(f4,axiom,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.58/0.58  fof(f260,plain,(
% 1.58/0.58    spl7_25 | ~spl7_3 | ~spl7_11),
% 1.58/0.58    inference(avatar_split_clause,[],[f204,f157,f117,f257])).
% 1.58/0.58  fof(f204,plain,(
% 1.58/0.58    l1_pre_topc(sK3) | (~spl7_3 | ~spl7_11)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f159,f119,f75])).
% 1.58/0.58  fof(f75,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f19])).
% 1.58/0.58  fof(f19,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f6])).
% 1.58/0.58  fof(f6,axiom,(
% 1.58/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.58/0.58  fof(f255,plain,(
% 1.58/0.58    spl7_24 | ~spl7_3 | ~spl7_10),
% 1.58/0.58    inference(avatar_split_clause,[],[f203,f152,f117,f252])).
% 1.58/0.58  fof(f203,plain,(
% 1.58/0.58    l1_pre_topc(sK2) | (~spl7_3 | ~spl7_10)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f154,f119,f75])).
% 1.58/0.58  fof(f235,plain,(
% 1.58/0.58    ~spl7_20 | ~spl7_21),
% 1.58/0.58    inference(avatar_split_clause,[],[f73,f220,f216])).
% 1.58/0.58  fof(f73,plain,(
% 1.58/0.58    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f48,plain,(
% 1.58/0.58    (((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f47,f46,f45,f44,f43,f42,f41])).
% 1.58/0.58  fof(f41,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f42,plain,(
% 1.58/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f43,plain,(
% 1.58/0.58    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f44,plain,(
% 1.58/0.58    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f45,plain,(
% 1.58/0.58    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f46,plain,(
% 1.58/0.58    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f47,plain,(
% 1.58/0.58    ? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/0.58    inference(flattening,[],[f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/0.58    inference(nnf_transformation,[],[f17])).
% 1.58/0.58  fof(f17,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/0.58    inference(flattening,[],[f16])).
% 1.58/0.58  fof(f16,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f15])).
% 1.58/0.58  fof(f15,negated_conjecture,(
% 1.58/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.58/0.58    inference(negated_conjecture,[],[f14])).
% 1.58/0.58  fof(f14,conjecture,(
% 1.58/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.58/0.58  fof(f229,plain,(
% 1.58/0.58    spl7_22 | ~spl7_14 | ~spl7_21),
% 1.58/0.58    inference(avatar_split_clause,[],[f224,f220,f172,f226])).
% 1.58/0.58  fof(f224,plain,(
% 1.58/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | (~spl7_14 | ~spl7_21)),
% 1.58/0.58    inference(forward_demodulation,[],[f222,f174])).
% 1.58/0.58  fof(f222,plain,(
% 1.58/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl7_21),
% 1.58/0.58    inference(avatar_component_clause,[],[f220])).
% 1.58/0.58  fof(f223,plain,(
% 1.58/0.58    spl7_20 | spl7_21),
% 1.58/0.58    inference(avatar_split_clause,[],[f72,f220,f216])).
% 1.58/0.58  fof(f72,plain,(
% 1.58/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f197,plain,(
% 1.58/0.58    spl7_18),
% 1.58/0.58    inference(avatar_split_clause,[],[f66,f194])).
% 1.58/0.58  fof(f66,plain,(
% 1.58/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f190,plain,(
% 1.58/0.58    spl7_17),
% 1.58/0.58    inference(avatar_split_clause,[],[f65,f187])).
% 1.58/0.58  fof(f65,plain,(
% 1.58/0.58    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f185,plain,(
% 1.58/0.58    spl7_16),
% 1.58/0.58    inference(avatar_split_clause,[],[f101,f182])).
% 1.58/0.58  fof(f101,plain,(
% 1.58/0.58    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.58/0.58    inference(forward_demodulation,[],[f70,f71])).
% 1.58/0.58  fof(f71,plain,(
% 1.58/0.58    sK5 = sK6),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f70,plain,(
% 1.58/0.58    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f180,plain,(
% 1.58/0.58    spl7_15),
% 1.58/0.58    inference(avatar_split_clause,[],[f69,f177])).
% 1.58/0.58  fof(f69,plain,(
% 1.58/0.58    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f175,plain,(
% 1.58/0.58    spl7_14),
% 1.58/0.58    inference(avatar_split_clause,[],[f71,f172])).
% 1.58/0.58  fof(f170,plain,(
% 1.58/0.58    spl7_13),
% 1.58/0.58    inference(avatar_split_clause,[],[f68,f167])).
% 1.58/0.58  fof(f68,plain,(
% 1.58/0.58    m1_pre_topc(sK2,sK3)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f165,plain,(
% 1.58/0.58    spl7_12),
% 1.58/0.58    inference(avatar_split_clause,[],[f67,f162])).
% 1.58/0.58  fof(f67,plain,(
% 1.58/0.58    v1_tsep_1(sK2,sK3)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f160,plain,(
% 1.58/0.58    spl7_11),
% 1.58/0.58    inference(avatar_split_clause,[],[f63,f157])).
% 1.58/0.58  fof(f63,plain,(
% 1.58/0.58    m1_pre_topc(sK3,sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f155,plain,(
% 1.58/0.58    spl7_10),
% 1.58/0.58    inference(avatar_split_clause,[],[f61,f152])).
% 1.58/0.58  fof(f61,plain,(
% 1.58/0.58    m1_pre_topc(sK2,sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f150,plain,(
% 1.58/0.58    spl7_9),
% 1.58/0.58    inference(avatar_split_clause,[],[f64,f147])).
% 1.58/0.58  fof(f64,plain,(
% 1.58/0.58    v1_funct_1(sK4)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f145,plain,(
% 1.58/0.58    ~spl7_8),
% 1.58/0.58    inference(avatar_split_clause,[],[f62,f142])).
% 1.58/0.58  fof(f62,plain,(
% 1.58/0.58    ~v2_struct_0(sK3)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f140,plain,(
% 1.58/0.58    ~spl7_7),
% 1.58/0.58    inference(avatar_split_clause,[],[f60,f137])).
% 1.58/0.58  fof(f60,plain,(
% 1.58/0.58    ~v2_struct_0(sK2)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f135,plain,(
% 1.58/0.58    spl7_6),
% 1.58/0.58    inference(avatar_split_clause,[],[f59,f132])).
% 1.58/0.58  fof(f59,plain,(
% 1.58/0.58    l1_pre_topc(sK1)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f130,plain,(
% 1.58/0.58    spl7_5),
% 1.58/0.58    inference(avatar_split_clause,[],[f58,f127])).
% 1.58/0.58  fof(f58,plain,(
% 1.58/0.58    v2_pre_topc(sK1)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f125,plain,(
% 1.58/0.58    ~spl7_4),
% 1.58/0.58    inference(avatar_split_clause,[],[f57,f122])).
% 1.58/0.58  fof(f57,plain,(
% 1.58/0.58    ~v2_struct_0(sK1)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f120,plain,(
% 1.58/0.58    spl7_3),
% 1.58/0.58    inference(avatar_split_clause,[],[f56,f117])).
% 1.58/0.58  fof(f56,plain,(
% 1.58/0.58    l1_pre_topc(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f115,plain,(
% 1.58/0.58    spl7_2),
% 1.58/0.58    inference(avatar_split_clause,[],[f55,f112])).
% 1.58/0.58  fof(f55,plain,(
% 1.58/0.58    v2_pre_topc(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f110,plain,(
% 1.58/0.58    ~spl7_1),
% 1.58/0.58    inference(avatar_split_clause,[],[f54,f107])).
% 1.58/0.58  fof(f54,plain,(
% 1.58/0.58    ~v2_struct_0(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (4649)------------------------------
% 1.58/0.58  % (4649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (4649)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (4649)Memory used [KB]: 11129
% 1.58/0.58  % (4649)Time elapsed: 0.111 s
% 1.58/0.58  % (4649)------------------------------
% 1.58/0.58  % (4649)------------------------------
% 1.58/0.58  % (4633)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.58/0.58  % (4618)Success in time 0.218 s
%------------------------------------------------------------------------------
