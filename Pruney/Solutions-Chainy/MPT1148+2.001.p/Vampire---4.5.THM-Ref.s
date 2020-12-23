%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 163 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  329 ( 618 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f75,f91,f95,f99,f104,f110,f121,f133,f141,f162,f168,f179,f184,f185])).

fof(f185,plain,
    ( ~ spl2_2
    | ~ spl2_22
    | spl2_30 ),
    inference(avatar_split_clause,[],[f183,f176,f139,f46])).

fof(f46,plain,
    ( spl2_2
  <=> r2_wellord1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f139,plain,
    ( spl2_22
  <=> ! [X3] :
        ( ~ r2_wellord1(u1_orders_2(sK0),X3)
        | r6_relat_2(u1_orders_2(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f176,plain,
    ( spl2_30
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f183,plain,
    ( ~ r2_wellord1(u1_orders_2(sK0),sK1)
    | ~ spl2_22
    | spl2_30 ),
    inference(resolution,[],[f178,f140])).

fof(f140,plain,
    ( ! [X3] :
        ( r6_relat_2(u1_orders_2(sK0),X3)
        | ~ r2_wellord1(u1_orders_2(sK0),X3) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f178,plain,
    ( ~ r6_relat_2(u1_orders_2(sK0),sK1)
    | spl2_30 ),
    inference(avatar_component_clause,[],[f176])).

fof(f184,plain,
    ( ~ spl2_2
    | ~ spl2_17
    | spl2_29 ),
    inference(avatar_split_clause,[],[f181,f172,f119,f46])).

fof(f119,plain,
    ( spl2_17
  <=> ! [X0] :
        ( ~ r2_wellord1(u1_orders_2(sK0),X0)
        | r1_relat_2(u1_orders_2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f172,plain,
    ( spl2_29
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f181,plain,
    ( ~ r2_wellord1(u1_orders_2(sK0),sK1)
    | ~ spl2_17
    | spl2_29 ),
    inference(resolution,[],[f174,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( r1_relat_2(u1_orders_2(sK0),X0)
        | ~ r2_wellord1(u1_orders_2(sK0),X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f174,plain,
    ( ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | spl2_29 ),
    inference(avatar_component_clause,[],[f172])).

fof(f179,plain,
    ( ~ spl2_16
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_14
    | spl2_28 ),
    inference(avatar_split_clause,[],[f170,f165,f97,f176,f172,f107])).

fof(f107,plain,
    ( spl2_16
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f97,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( r7_relat_2(X1,X0)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f165,plain,
    ( spl2_28
  <=> r7_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f170,plain,
    ( ~ r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl2_14
    | spl2_28 ),
    inference(resolution,[],[f167,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r7_relat_2(X1,X0)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f167,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f165])).

fof(f168,plain,
    ( ~ spl2_28
    | ~ spl2_3
    | spl2_4
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f163,f160,f56,f51,f165])).

fof(f51,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( spl2_4
  <=> v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f160,plain,
    ( spl2_27
  <=> ! [X0] :
        ( ~ r7_relat_2(u1_orders_2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v6_orders_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | spl2_4
    | ~ spl2_27 ),
    inference(resolution,[],[f161,f58])).

fof(f58,plain,
    ( ~ v6_orders_2(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f161,plain,
    ( ! [X0] :
        ( v6_orders_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r7_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f142,f131,f41,f160])).

fof(f41,plain,
    ( spl2_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f131,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( v6_orders_2(X1,X0)
        | ~ r7_relat_2(u1_orders_2(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r7_relat_2(u1_orders_2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v6_orders_2(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_20 ),
    inference(resolution,[],[f132,f43])).

fof(f43,plain,
    ( l1_orders_2(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ r7_relat_2(u1_orders_2(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v6_orders_2(X1,X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f141,plain,
    ( spl2_22
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f114,f107,f73,f139])).

fof(f73,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r6_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f114,plain,
    ( ! [X3] :
        ( ~ r2_wellord1(u1_orders_2(sK0),X3)
        | r6_relat_2(u1_orders_2(sK0),X3) )
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(resolution,[],[f109,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_wellord1(X0,X1)
        | r6_relat_2(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f109,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f133,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f29,f131])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f121,plain,
    ( spl2_17
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f111,f107,f61,f119])).

fof(f61,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_relat_2(X0,X1)
        | ~ r2_wellord1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_wellord1(u1_orders_2(sK0),X0)
        | r1_relat_2(u1_orders_2(sK0),X0) )
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(resolution,[],[f109,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r2_wellord1(X0,X1)
        | r1_relat_2(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f110,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f105,f102,f41,f107])).

fof(f102,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | v1_relat_1(u1_orders_2(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f105,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl2_1
    | ~ spl2_15 ),
    inference(resolution,[],[f103,f43])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | v1_relat_1(u1_orders_2(X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl2_15
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f100,f93,f89,f102])).

fof(f89,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X0] :
        ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | v1_relat_1(u1_orders_2(X0)) )
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(resolution,[],[f94,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f94,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        | ~ l1_orders_2(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X1,X0)
      | ~ r6_relat_2(X1,X0)
      | ~ r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f93])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f91,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f75,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

fof(f63,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f26,f51,f56])).

fof(f26,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK1,sK0) )
    & r2_wellord1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r2_wellord1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X1,sK0) )
          & r2_wellord1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v6_orders_2(X1,sK0) )
        & r2_wellord1(u1_orders_2(sK0),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(sK1,sK0) )
      & r2_wellord1(u1_orders_2(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_wellord1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_wellord1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    r2_wellord1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.44  % (2879)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.19/0.44  % (2872)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.45  % (2884)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.19/0.45  % (2884)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f186,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f63,f75,f91,f95,f99,f104,f110,f121,f133,f141,f162,f168,f179,f184,f185])).
% 0.19/0.45  fof(f185,plain,(
% 0.19/0.45    ~spl2_2 | ~spl2_22 | spl2_30),
% 0.19/0.45    inference(avatar_split_clause,[],[f183,f176,f139,f46])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    spl2_2 <=> r2_wellord1(u1_orders_2(sK0),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    spl2_22 <=> ! [X3] : (~r2_wellord1(u1_orders_2(sK0),X3) | r6_relat_2(u1_orders_2(sK0),X3))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.19/0.45  fof(f176,plain,(
% 0.19/0.45    spl2_30 <=> r6_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.19/0.45  fof(f183,plain,(
% 0.19/0.45    ~r2_wellord1(u1_orders_2(sK0),sK1) | (~spl2_22 | spl2_30)),
% 0.19/0.45    inference(resolution,[],[f178,f140])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    ( ! [X3] : (r6_relat_2(u1_orders_2(sK0),X3) | ~r2_wellord1(u1_orders_2(sK0),X3)) ) | ~spl2_22),
% 0.19/0.45    inference(avatar_component_clause,[],[f139])).
% 0.19/0.45  fof(f178,plain,(
% 0.19/0.45    ~r6_relat_2(u1_orders_2(sK0),sK1) | spl2_30),
% 0.19/0.45    inference(avatar_component_clause,[],[f176])).
% 0.19/0.45  fof(f184,plain,(
% 0.19/0.45    ~spl2_2 | ~spl2_17 | spl2_29),
% 0.19/0.45    inference(avatar_split_clause,[],[f181,f172,f119,f46])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    spl2_17 <=> ! [X0] : (~r2_wellord1(u1_orders_2(sK0),X0) | r1_relat_2(u1_orders_2(sK0),X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.45  fof(f172,plain,(
% 0.19/0.45    spl2_29 <=> r1_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.19/0.45  fof(f181,plain,(
% 0.19/0.45    ~r2_wellord1(u1_orders_2(sK0),sK1) | (~spl2_17 | spl2_29)),
% 0.19/0.45    inference(resolution,[],[f174,f120])).
% 0.19/0.45  fof(f120,plain,(
% 0.19/0.45    ( ! [X0] : (r1_relat_2(u1_orders_2(sK0),X0) | ~r2_wellord1(u1_orders_2(sK0),X0)) ) | ~spl2_17),
% 0.19/0.45    inference(avatar_component_clause,[],[f119])).
% 0.19/0.45  fof(f174,plain,(
% 0.19/0.45    ~r1_relat_2(u1_orders_2(sK0),sK1) | spl2_29),
% 0.19/0.45    inference(avatar_component_clause,[],[f172])).
% 0.19/0.45  fof(f179,plain,(
% 0.19/0.45    ~spl2_16 | ~spl2_29 | ~spl2_30 | ~spl2_14 | spl2_28),
% 0.19/0.45    inference(avatar_split_clause,[],[f170,f165,f97,f176,f172,f107])).
% 0.19/0.45  fof(f107,plain,(
% 0.19/0.45    spl2_16 <=> v1_relat_1(u1_orders_2(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    spl2_14 <=> ! [X1,X0] : (r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.45  fof(f165,plain,(
% 0.19/0.45    spl2_28 <=> r7_relat_2(u1_orders_2(sK0),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.19/0.45  fof(f170,plain,(
% 0.19/0.45    ~r6_relat_2(u1_orders_2(sK0),sK1) | ~r1_relat_2(u1_orders_2(sK0),sK1) | ~v1_relat_1(u1_orders_2(sK0)) | (~spl2_14 | spl2_28)),
% 0.19/0.45    inference(resolution,[],[f167,f98])).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_14),
% 0.19/0.45    inference(avatar_component_clause,[],[f97])).
% 0.19/0.45  fof(f167,plain,(
% 0.19/0.45    ~r7_relat_2(u1_orders_2(sK0),sK1) | spl2_28),
% 0.19/0.45    inference(avatar_component_clause,[],[f165])).
% 0.19/0.45  fof(f168,plain,(
% 0.19/0.45    ~spl2_28 | ~spl2_3 | spl2_4 | ~spl2_27),
% 0.19/0.45    inference(avatar_split_clause,[],[f163,f160,f56,f51,f165])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    spl2_4 <=> v6_orders_2(sK1,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.45  fof(f160,plain,(
% 0.19/0.45    spl2_27 <=> ! [X0] : (~r7_relat_2(u1_orders_2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v6_orders_2(X0,sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.19/0.45  fof(f163,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r7_relat_2(u1_orders_2(sK0),sK1) | (spl2_4 | ~spl2_27)),
% 0.19/0.45    inference(resolution,[],[f161,f58])).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    ~v6_orders_2(sK1,sK0) | spl2_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f56])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    ( ! [X0] : (v6_orders_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r7_relat_2(u1_orders_2(sK0),X0)) ) | ~spl2_27),
% 0.19/0.45    inference(avatar_component_clause,[],[f160])).
% 0.19/0.45  fof(f162,plain,(
% 0.19/0.45    spl2_27 | ~spl2_1 | ~spl2_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f142,f131,f41,f160])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    spl2_1 <=> l1_orders_2(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.45  fof(f131,plain,(
% 0.19/0.45    spl2_20 <=> ! [X1,X0] : (v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.19/0.45  fof(f142,plain,(
% 0.19/0.45    ( ! [X0] : (~r7_relat_2(u1_orders_2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v6_orders_2(X0,sK0)) ) | (~spl2_1 | ~spl2_20)),
% 0.19/0.45    inference(resolution,[],[f132,f43])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    l1_orders_2(sK0) | ~spl2_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f41])).
% 0.19/0.45  fof(f132,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r7_relat_2(u1_orders_2(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v6_orders_2(X1,X0)) ) | ~spl2_20),
% 0.19/0.45    inference(avatar_component_clause,[],[f131])).
% 0.19/0.45  fof(f141,plain,(
% 0.19/0.45    spl2_22 | ~spl2_8 | ~spl2_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f114,f107,f73,f139])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    spl2_8 <=> ! [X1,X0] : (r6_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    ( ! [X3] : (~r2_wellord1(u1_orders_2(sK0),X3) | r6_relat_2(u1_orders_2(sK0),X3)) ) | (~spl2_8 | ~spl2_16)),
% 0.19/0.45    inference(resolution,[],[f109,f74])).
% 0.19/0.45  fof(f74,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_wellord1(X0,X1) | r6_relat_2(X0,X1)) ) | ~spl2_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f73])).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    v1_relat_1(u1_orders_2(sK0)) | ~spl2_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f107])).
% 0.19/0.45  fof(f133,plain,(
% 0.19/0.45    spl2_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f29,f131])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    spl2_17 | ~spl2_5 | ~spl2_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f111,f107,f61,f119])).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    spl2_5 <=> ! [X1,X0] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_wellord1(u1_orders_2(sK0),X0) | r1_relat_2(u1_orders_2(sK0),X0)) ) | (~spl2_5 | ~spl2_16)),
% 0.19/0.45    inference(resolution,[],[f109,f62])).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_wellord1(X0,X1) | r1_relat_2(X0,X1)) ) | ~spl2_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f61])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    spl2_16 | ~spl2_1 | ~spl2_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f105,f102,f41,f107])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    spl2_15 <=> ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    v1_relat_1(u1_orders_2(sK0)) | (~spl2_1 | ~spl2_15)),
% 0.19/0.45    inference(resolution,[],[f103,f43])).
% 0.19/0.45  fof(f103,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0))) ) | ~spl2_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f102])).
% 0.19/0.45  fof(f104,plain,(
% 0.19/0.45    spl2_15 | ~spl2_12 | ~spl2_13),
% 0.19/0.45    inference(avatar_split_clause,[],[f100,f93,f89,f102])).
% 0.19/0.45  fof(f89,plain,(
% 0.19/0.45    spl2_12 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.45  fof(f93,plain,(
% 0.19/0.45    spl2_13 <=> ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.19/0.45  fof(f100,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0))) ) | (~spl2_12 | ~spl2_13)),
% 0.19/0.45    inference(resolution,[],[f94,f90])).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl2_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f89])).
% 0.19/0.45  fof(f94,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) ) | ~spl2_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f93])).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    spl2_14),
% 0.19/0.45    inference(avatar_split_clause,[],[f38,f97])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ! [X0,X1] : (((r7_relat_2(X1,X0) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0)) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(flattening,[],[f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0,X1] : (((r7_relat_2(X1,X0) | (~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0))) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~r7_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(nnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).
% 0.19/0.45  fof(f95,plain,(
% 0.19/0.45    spl2_13),
% 0.19/0.45    inference(avatar_split_clause,[],[f27,f93])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.19/0.45  fof(f91,plain,(
% 0.19/0.45    spl2_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f39,f89])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    spl2_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f33,f73])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r6_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(flattening,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | (~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    spl2_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f30,f61])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    ~spl2_4 | ~spl2_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f26,f51,f56])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)) & r2_wellord1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X1,sK0)) & r2_wellord1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X1,sK0)) & r2_wellord1(u1_orders_2(sK0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK1,sK0)) & r2_wellord1(u1_orders_2(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0))),
% 0.19/0.45    inference(flattening,[],[f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_wellord1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.19/0.45    inference(negated_conjecture,[],[f6])).
% 0.19/0.45  fof(f6,conjecture,(
% 0.19/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_wellord1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    spl2_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f51])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f25,f46])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    r2_wellord1(u1_orders_2(sK0),sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    spl2_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f41])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    l1_orders_2(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (2884)------------------------------
% 0.19/0.45  % (2884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (2884)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (2884)Memory used [KB]: 5373
% 0.19/0.45  % (2884)Time elapsed: 0.054 s
% 0.19/0.45  % (2884)------------------------------
% 0.19/0.45  % (2884)------------------------------
% 0.19/0.45  % (2867)Success in time 0.105 s
%------------------------------------------------------------------------------
