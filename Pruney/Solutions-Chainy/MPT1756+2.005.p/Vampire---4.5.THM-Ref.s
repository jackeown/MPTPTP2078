%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 276 expanded)
%              Number of leaves         :   31 ( 121 expanded)
%              Depth                    :    7
%              Number of atoms          :  553 (2296 expanded)
%              Number of equality atoms :   14 ( 101 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f149,f150,f157,f162,f184,f220,f222,f225,f258,f268,f272])).

fof(f272,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_17
    | spl8_42 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_17
    | spl8_42 ),
    inference(unit_resulting_resolution,[],[f74,f69,f129,f49,f134,f109,f109,f267,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f267,plain,
    ( ~ r2_hidden(sK5,k1_tops_1(sK1,sK4))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl8_42
  <=> r2_hidden(sK5,k1_tops_1(sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

% (16183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f134,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_17
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f129,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_16
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f69,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f268,plain,
    ( spl8_6
    | ~ spl8_42
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_4
    | ~ spl8_5
    | spl8_40 ),
    inference(avatar_split_clause,[],[f263,f255,f72,f67,f112,f107,f265,f77])).

fof(f77,plain,
    ( spl8_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f112,plain,
    ( spl8_13
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f255,plain,
    ( spl8_40
  <=> m1_connsp_2(sK4,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f263,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK5,k1_tops_1(sK1,sK4))
    | v2_struct_0(sK1)
    | spl8_40 ),
    inference(resolution,[],[f257,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f257,plain,
    ( ~ m1_connsp_2(sK4,sK1,sK5)
    | spl8_40 ),
    inference(avatar_component_clause,[],[f255])).

fof(f258,plain,
    ( ~ spl8_40
    | ~ spl8_15
    | ~ spl8_12
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f252,f218,f107,f122,f255])).

fof(f122,plain,
    ( spl8_15
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f218,plain,
    ( spl8_33
  <=> ! [X2] :
        ( ~ m1_connsp_2(X2,sK1,sK5)
        | ~ r1_tarski(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f252,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_connsp_2(sK4,sK1,sK5)
    | ~ spl8_12
    | ~ spl8_33 ),
    inference(resolution,[],[f219,f109])).

fof(f219,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X2,u1_struct_0(sK3))
        | ~ m1_connsp_2(X2,sK1,sK5) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f218])).

fof(f225,plain,
    ( ~ spl8_19
    | spl8_3
    | ~ spl8_21
    | ~ spl8_13
    | spl8_33
    | ~ spl8_10
    | spl8_11
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_1
    | ~ spl8_2
    | spl8_22 ),
    inference(avatar_split_clause,[],[f223,f159,f57,f52,f77,f72,f67,f92,f87,f82,f102,f97,f218,f112,f154,f62,f142])).

fof(f142,plain,
    ( spl8_19
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f62,plain,
    ( spl8_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f154,plain,
    ( spl8_21
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f97,plain,
    ( spl8_10
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f102,plain,
    ( spl8_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f82,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f87,plain,
    ( spl8_8
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f92,plain,
    ( spl8_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f52,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f57,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f159,plain,
    ( spl8_22
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK5)
        | v2_struct_0(sK0)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    | spl8_22 ),
    inference(resolution,[],[f160,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | v2_struct_0(X0)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f160,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f159])).

fof(f222,plain,
    ( ~ spl8_22
    | ~ spl8_14
    | spl8_20 ),
    inference(avatar_split_clause,[],[f221,f146,f117,f159])).

fof(f117,plain,
    ( spl8_14
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f146,plain,
    ( spl8_20
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f221,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl8_14
    | spl8_20 ),
    inference(forward_demodulation,[],[f148,f119])).

fof(f119,plain,
    ( sK5 = sK6
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f148,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f220,plain,
    ( ~ spl8_10
    | ~ spl8_21
    | spl8_33
    | ~ spl8_22
    | spl8_11
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f188,f182,f102,f159,f218,f154,f97])).

fof(f182,plain,
    ( spl8_25
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f188,plain,
    ( ! [X2] :
        ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | ~ m1_connsp_2(X2,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X2,u1_struct_0(sK3))
        | ~ m1_pre_topc(sK3,sK1) )
    | spl8_11
    | ~ spl8_25 ),
    inference(resolution,[],[f183,f104])).

fof(f104,plain,
    ( ~ v2_struct_0(sK3)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f182])).

fof(f184,plain,
    ( spl8_3
    | ~ spl8_13
    | spl8_25
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_1
    | ~ spl8_2
    | spl8_19 ),
    inference(avatar_split_clause,[],[f180,f142,f57,f52,f77,f72,f67,f92,f87,f82,f182,f112,f62])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | ~ m1_connsp_2(X1,sK1,sK5)
        | ~ r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | v2_struct_0(sK0) )
    | spl8_19 ),
    inference(resolution,[],[f48,f144])).

fof(f144,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f162,plain,
    ( spl8_22
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f152,f146,f117,f159])).

fof(f152,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f147,f119])).

fof(f147,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f157,plain,
    ( spl8_21
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f151,f137,f117,f154])).

fof(f137,plain,
    ( spl8_18
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f151,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_14
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f139,f119])).

fof(f139,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f150,plain,
    ( spl8_19
    | spl8_20 ),
    inference(avatar_split_clause,[],[f15,f146,f142])).

fof(f15,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

% (16202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f149,plain,
    ( ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f16,f146,f142])).

fof(f16,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f140,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f17,f137])).

fof(f17,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f135,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f18,f132])).

fof(f18,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f130,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f19,f127])).

fof(f19,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f125,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f20,f122])).

fof(f20,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f120,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f21,f117])).

fof(f21,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f8])).

fof(f115,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f22,f112])).

fof(f22,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f110,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f23,f107])).

fof(f23,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f105,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f24,f102])).

fof(f24,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f100,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f25,f97])).

fof(f25,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f95,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f26,f92])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f27,f87])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16197)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (16189)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (16186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (16194)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (16185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (16197)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (16195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f149,f150,f157,f162,f184,f220,f222,f225,f258,f268,f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_16 | ~spl8_17 | spl8_42),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    $false | (~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_16 | ~spl8_17 | spl8_42)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f74,f69,f129,f49,f134,f109,f109,f267,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | ~v2_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_tops_1(sK1,sK4)) | spl8_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f265])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    spl8_42 <=> r2_hidden(sK5,k1_tops_1(sK1,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.21/0.49  % (16183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl8_12 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    v3_pre_topc(sK4,sK1) | ~spl8_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl8_17 <=> v3_pre_topc(sK4,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    r2_hidden(sK5,sK4) | ~spl8_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl8_16 <=> r2_hidden(sK5,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    l1_pre_topc(sK1) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl8_4 <=> l1_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v2_pre_topc(sK1) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl8_5 <=> v2_pre_topc(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    spl8_6 | ~spl8_42 | ~spl8_12 | ~spl8_13 | ~spl8_4 | ~spl8_5 | spl8_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f263,f255,f72,f67,f112,f107,f265,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl8_6 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl8_13 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl8_40 <=> m1_connsp_2(sK4,sK1,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK5,k1_tops_1(sK1,sK4)) | v2_struct_0(sK1) | spl8_40),
% 0.21/0.49    inference(resolution,[],[f257,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ~m1_connsp_2(sK4,sK1,sK5) | spl8_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f255])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ~spl8_40 | ~spl8_15 | ~spl8_12 | ~spl8_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f252,f218,f107,f122,f255])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl8_15 <=> r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl8_33 <=> ! [X2] : (~m1_connsp_2(X2,sK1,sK5) | ~r1_tarski(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~r1_tarski(sK4,u1_struct_0(sK3)) | ~m1_connsp_2(sK4,sK1,sK5) | (~spl8_12 | ~spl8_33)),
% 0.21/0.49    inference(resolution,[],[f219,f109])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X2,u1_struct_0(sK3)) | ~m1_connsp_2(X2,sK1,sK5)) ) | ~spl8_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~spl8_19 | spl8_3 | ~spl8_21 | ~spl8_13 | spl8_33 | ~spl8_10 | spl8_11 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_1 | ~spl8_2 | spl8_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f159,f57,f52,f77,f72,f67,f92,f87,f82,f102,f97,f218,f112,f154,f62,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl8_19 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl8_3 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl8_21 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl8_10 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl8_11 <=> v2_struct_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl8_8 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl8_9 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl8_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl8_2 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl8_22 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK5) | v2_struct_0(sK0) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) ) | spl8_22),
% 0.21/0.49    inference(resolution,[],[f160,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | v2_struct_0(X0) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 0.21/0.49    inference(equality_resolution,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl8_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~spl8_22 | ~spl8_14 | spl8_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f221,f146,f117,f159])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl8_14 <=> sK5 = sK6),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl8_20 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (~spl8_14 | spl8_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f148,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK5 = sK6 | ~spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | spl8_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~spl8_10 | ~spl8_21 | spl8_33 | ~spl8_22 | spl8_11 | ~spl8_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f188,f182,f102,f159,f218,f154,f97])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl8_25 <=> ! [X1,X0] : (v2_struct_0(X0) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~m1_connsp_2(X1,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_connsp_2(X2,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X2,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1)) ) | (spl8_11 | ~spl8_25)),
% 0.21/0.49    inference(resolution,[],[f183,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~v2_struct_0(sK3) | spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~m1_connsp_2(X1,sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1)) ) | ~spl8_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl8_3 | ~spl8_13 | spl8_25 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_1 | ~spl8_2 | spl8_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f180,f142,f57,f52,f77,f72,f67,f92,f87,f82,f182,f112,f62])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | v2_struct_0(sK0)) ) | spl8_19),
% 0.21/0.49    inference(resolution,[],[f48,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl8_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl8_22 | ~spl8_14 | ~spl8_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f146,f117,f159])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (~spl8_14 | ~spl8_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f147,f119])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~spl8_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl8_21 | ~spl8_14 | ~spl8_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f137,f117,f154])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl8_18 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl8_14 | ~spl8_18)),
% 0.21/0.49    inference(backward_demodulation,[],[f139,f119])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl8_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl8_19 | spl8_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f146,f142])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.50  % (16202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ~spl8_19 | ~spl8_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f146,f142])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl8_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f137])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl8_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f132])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    v3_pre_topc(sK4,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl8_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f127])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    r2_hidden(sK5,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl8_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f122])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl8_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f117])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    sK5 = sK6),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl8_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f112])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl8_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f107])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f102])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f97])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl8_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f92])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f87])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f82])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f77])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f72])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v2_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f67])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    l1_pre_topc(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f62])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f57])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f52])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16197)------------------------------
% 0.21/0.50  % (16197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16197)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16197)Memory used [KB]: 6396
% 0.21/0.50  % (16197)Time elapsed: 0.082 s
% 0.21/0.50  % (16197)------------------------------
% 0.21/0.50  % (16197)------------------------------
% 0.21/0.50  % (16181)Success in time 0.139 s
%------------------------------------------------------------------------------
