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
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 362 expanded)
%              Number of leaves         :   38 ( 166 expanded)
%              Depth                    :   10
%              Number of atoms          :  709 (2619 expanded)
%              Number of equality atoms :   12 (  99 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f148,f149,f155,f163,f189,f195,f201,f207,f213,f219,f225,f231,f277,f283,f285,f292,f295])).

fof(f295,plain,
    ( ~ spl12_10
    | ~ spl12_21
    | ~ spl12_13
    | spl12_22
    | ~ spl12_19
    | spl12_11
    | ~ spl12_28
    | ~ spl12_39 ),
    inference(avatar_split_clause,[],[f294,f289,f211,f101,f141,f160,f111,f152,f96])).

fof(f96,plain,
    ( spl12_10
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f152,plain,
    ( spl12_21
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f111,plain,
    ( spl12_13
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f160,plain,
    ( spl12_22
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f141,plain,
    ( spl12_19
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f101,plain,
    ( spl12_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f211,plain,
    ( spl12_28
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ sP10(X0,sK1,X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f289,plain,
    ( spl12_39
  <=> sP10(sK3,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f294,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl12_28
    | ~ spl12_39 ),
    inference(resolution,[],[f291,f212])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ sP10(X0,sK1,X1)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f211])).

fof(f291,plain,
    ( sP10(sK3,sK1,sK5)
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f289])).

fof(f292,plain,
    ( spl12_39
    | ~ spl12_29
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(avatar_split_clause,[],[f287,f274,f228,f216,f289])).

fof(f216,plain,
    ( spl12_29
  <=> m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f228,plain,
    ( spl12_31
  <=> m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f274,plain,
    ( spl12_38
  <=> r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f287,plain,
    ( sP10(sK3,sK1,sK5)
    | ~ spl12_29
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(resolution,[],[f279,f218])).

fof(f218,plain,
    ( m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5)
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f216])).

fof(f279,plain,
    ( ! [X1] :
        ( ~ m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X1)
        | sP10(sK3,sK1,X1) )
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(resolution,[],[f276,f237])).

fof(f237,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(X3))
        | ~ m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X4)
        | sP10(X3,sK1,X4) )
    | ~ spl12_31 ),
    inference(resolution,[],[f230,f46])).

fof(f46,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP10(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f46_D])).

% (24449)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f46_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP10(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f230,plain,
    ( m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f228])).

fof(f276,plain,
    ( r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f274])).

fof(f285,plain,
    ( ~ spl12_22
    | ~ spl12_14
    | spl12_20 ),
    inference(avatar_split_clause,[],[f284,f145,f116,f160])).

fof(f116,plain,
    ( spl12_14
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f145,plain,
    ( spl12_20
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f284,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl12_14
    | spl12_20 ),
    inference(forward_demodulation,[],[f147,f118])).

fof(f118,plain,
    ( sK5 = sK6
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f147,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | spl12_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f283,plain,
    ( spl12_30
    | ~ spl12_29
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(avatar_split_clause,[],[f282,f274,f228,f216,f222])).

fof(f222,plain,
    ( spl12_30
  <=> sP11(sK3,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f282,plain,
    ( sP11(sK3,sK1,sK5)
    | ~ spl12_29
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(resolution,[],[f278,f218])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X0)
        | sP11(sK3,sK1,X0) )
    | ~ spl12_31
    | ~ spl12_38 ),
    inference(resolution,[],[f276,f238])).

fof(f238,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(X5))
        | ~ m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X6)
        | sP11(X5,sK1,X6) )
    | ~ spl12_31 ),
    inference(resolution,[],[f230,f48])).

fof(f48,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP11(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f48_D])).

fof(f48_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP11(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f277,plain,
    ( spl12_38
    | ~ spl12_15
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f272,f204,f121,f274])).

fof(f121,plain,
    ( spl12_15
  <=> r1_tarski(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f204,plain,
    ( spl12_27
  <=> r1_tarski(sK8(sK1,sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f272,plain,
    ( r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))
    | ~ spl12_15
    | ~ spl12_27 ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))
    | r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))
    | ~ spl12_15
    | ~ spl12_27 ),
    inference(resolution,[],[f268,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f268,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),u1_struct_0(sK3))
        | r1_tarski(sK8(sK1,sK4,sK5),X0) )
    | ~ spl12_15
    | ~ spl12_27 ),
    inference(resolution,[],[f266,f123])).

fof(f123,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK4,X1)
        | r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),X1)
        | r1_tarski(sK8(sK1,sK4,sK5),X0) )
    | ~ spl12_27 ),
    inference(resolution,[],[f208,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f208,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),sK4)
        | r1_tarski(sK8(sK1,sK4,sK5),X0) )
    | ~ spl12_27 ),
    inference(resolution,[],[f206,f165])).

fof(f165,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | r2_hidden(sK9(X1,X2),X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f206,plain,
    ( r1_tarski(sK8(sK1,sK4,sK5),sK4)
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f231,plain,
    ( ~ spl12_16
    | spl12_31
    | ~ spl12_13
    | ~ spl12_26 ),
    inference(avatar_split_clause,[],[f226,f199,f111,f228,f126])).

fof(f126,plain,
    ( spl12_16
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f199,plain,
    ( spl12_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f226,plain,
    ( m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK5,sK4)
    | ~ spl12_13
    | ~ spl12_26 ),
    inference(resolution,[],[f200,f113])).

fof(f113,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f225,plain,
    ( ~ spl12_30
    | spl12_19
    | spl12_3
    | ~ spl12_21
    | ~ spl12_13
    | ~ spl12_10
    | spl12_11
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f220,f160,f56,f51,f76,f71,f66,f91,f86,f81,f101,f96,f111,f152,f61,f141,f222])).

fof(f61,plain,
    ( spl12_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f81,plain,
    ( spl12_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f86,plain,
    ( spl12_8
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f91,plain,
    ( spl12_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f66,plain,
    ( spl12_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f71,plain,
    ( spl12_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f76,plain,
    ( spl12_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f51,plain,
    ( spl12_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f56,plain,
    ( spl12_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f220,plain,
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
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ sP11(sK3,sK1,sK5)
    | ~ spl12_22 ),
    inference(resolution,[],[f49,f162])).

fof(f162,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f49,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ sP11(X3,X1,X6) ) ),
    inference(general_splitting,[],[f45,f48_D])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f219,plain,
    ( ~ spl12_16
    | spl12_29
    | ~ spl12_13
    | ~ spl12_25 ),
    inference(avatar_split_clause,[],[f214,f193,f111,f216,f126])).

fof(f193,plain,
    ( spl12_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0)
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f214,plain,
    ( m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5)
    | ~ r2_hidden(sK5,sK4)
    | ~ spl12_13
    | ~ spl12_25 ),
    inference(resolution,[],[f194,f113])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f193])).

fof(f213,plain,
    ( spl12_28
    | spl12_3
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_4
    | ~ spl12_5
    | spl12_6
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f209,f81,f56,f51,f76,f71,f66,f91,f86,f61,f211])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1)
        | ~ r1_tmap_1(sK1,sK0,sK2,X1)
        | ~ sP10(X0,sK1,X1) )
    | ~ spl12_7 ),
    inference(resolution,[],[f47,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f47,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ sP10(X3,X1,X6) ) ),
    inference(general_splitting,[],[f44,f46_D])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
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
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f207,plain,
    ( ~ spl12_16
    | spl12_27
    | ~ spl12_13
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f202,f187,f111,f204,f126])).

fof(f187,plain,
    ( spl12_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(sK8(sK1,sK4,X0),sK4)
        | ~ r2_hidden(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f202,plain,
    ( r1_tarski(sK8(sK1,sK4,sK5),sK4)
    | ~ r2_hidden(sK5,sK4)
    | ~ spl12_13
    | ~ spl12_24 ),
    inference(resolution,[],[f188,f113])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tarski(sK8(sK1,sK4,X0),sK4)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f187])).

fof(f201,plain,
    ( ~ spl12_17
    | spl12_26
    | spl12_6
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f197,f106,f71,f66,f76,f199,f131])).

fof(f131,plain,
    ( spl12_17
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f106,plain,
    ( spl12_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK4)
        | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_pre_topc(sK4,sK1) )
    | ~ spl12_12 ),
    inference(resolution,[],[f34,f108])).

fof(f108,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f195,plain,
    ( ~ spl12_17
    | spl12_25
    | spl12_6
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f191,f106,f71,f66,f76,f193,f131])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK4)
        | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0)
        | ~ v3_pre_topc(sK4,sK1) )
    | ~ spl12_12 ),
    inference(resolution,[],[f35,f108])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(sK8(X0,X1,X2),X0,X2)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f189,plain,
    ( ~ spl12_17
    | spl12_24
    | spl12_6
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f185,f106,f71,f66,f76,f187,f131])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK4)
        | r1_tarski(sK8(sK1,sK4,X0),sK4)
        | ~ v3_pre_topc(sK4,sK1) )
    | ~ spl12_12 ),
    inference(resolution,[],[f36,f108])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_tarski(sK8(X0,X1,X2),X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f163,plain,
    ( spl12_22
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f158,f145,f116,f160])).

fof(f158,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(forward_demodulation,[],[f146,f118])).

fof(f146,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f155,plain,
    ( spl12_21
    | ~ spl12_14
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f150,f136,f116,f152])).

fof(f136,plain,
    ( spl12_18
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f150,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl12_14
    | ~ spl12_18 ),
    inference(forward_demodulation,[],[f138,f118])).

fof(f138,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f149,plain,
    ( spl12_19
    | spl12_20 ),
    inference(avatar_split_clause,[],[f13,f145,f141])).

% (24447)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f13,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f148,plain,
    ( ~ spl12_19
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f14,f145,f141])).

fof(f14,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f7])).

fof(f139,plain,(
    spl12_18 ),
    inference(avatar_split_clause,[],[f15,f136])).

fof(f15,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f134,plain,(
    spl12_17 ),
    inference(avatar_split_clause,[],[f16,f131])).

fof(f16,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f129,plain,(
    spl12_16 ),
    inference(avatar_split_clause,[],[f17,f126])).

fof(f17,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f7])).

fof(f124,plain,(
    spl12_15 ),
    inference(avatar_split_clause,[],[f18,f121])).

fof(f18,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f119,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f19,f116])).

fof(f19,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f7])).

fof(f114,plain,(
    spl12_13 ),
    inference(avatar_split_clause,[],[f20,f111])).

fof(f20,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f109,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f21,f106])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f104,plain,(
    ~ spl12_11 ),
    inference(avatar_split_clause,[],[f22,f101])).

fof(f22,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f99,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f23,f96])).

fof(f23,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    spl12_9 ),
    inference(avatar_split_clause,[],[f24,f91])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f25,f86])).

fof(f25,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ~ spl12_6 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ~ spl12_3 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (24435)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (24446)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (24451)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (24439)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (24462)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (24440)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24437)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24438)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (24463)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (24436)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (24454)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (24451)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (24443)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (24457)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (24455)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f148,f149,f155,f163,f189,f195,f201,f207,f213,f219,f225,f231,f277,f283,f285,f292,f295])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    ~spl12_10 | ~spl12_21 | ~spl12_13 | spl12_22 | ~spl12_19 | spl12_11 | ~spl12_28 | ~spl12_39),
% 0.20/0.52    inference(avatar_split_clause,[],[f294,f289,f211,f101,f141,f160,f111,f152,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl12_10 <=> m1_pre_topc(sK3,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    spl12_21 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl12_13 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    spl12_22 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl12_19 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    spl12_11 <=> v2_struct_0(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    spl12_28 <=> ! [X1,X0] : (v2_struct_0(X0) | ~sP10(X0,sK1,X1) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 0.20/0.52  fof(f289,plain,(
% 0.20/0.52    spl12_39 <=> sP10(sK3,sK1,sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    v2_struct_0(sK3) | ~r1_tmap_1(sK1,sK0,sK2,sK5) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1) | (~spl12_28 | ~spl12_39)),
% 0.20/0.52    inference(resolution,[],[f291,f212])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP10(X0,sK1,X1) | v2_struct_0(X0) | ~r1_tmap_1(sK1,sK0,sK2,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1)) ) | ~spl12_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f211])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    sP10(sK3,sK1,sK5) | ~spl12_39),
% 0.20/0.52    inference(avatar_component_clause,[],[f289])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    spl12_39 | ~spl12_29 | ~spl12_31 | ~spl12_38),
% 0.20/0.52    inference(avatar_split_clause,[],[f287,f274,f228,f216,f289])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    spl12_29 <=> m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    spl12_31 <=> m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    spl12_38 <=> r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).
% 0.20/0.52  fof(f287,plain,(
% 0.20/0.52    sP10(sK3,sK1,sK5) | (~spl12_29 | ~spl12_31 | ~spl12_38)),
% 0.20/0.52    inference(resolution,[],[f279,f218])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5) | ~spl12_29),
% 0.20/0.52    inference(avatar_component_clause,[],[f216])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X1) | sP10(sK3,sK1,X1)) ) | (~spl12_31 | ~spl12_38)),
% 0.20/0.52    inference(resolution,[],[f276,f237])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(X3)) | ~m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X4) | sP10(X3,sK1,X4)) ) | ~spl12_31),
% 0.20/0.52    inference(resolution,[],[f230,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP10(X3,X1,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46_D])).
% 0.20/0.52  % (24449)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  fof(f46_D,plain,(
% 0.20/0.52    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP10(X3,X1,X6)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl12_31),
% 0.20/0.52    inference(avatar_component_clause,[],[f228])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) | ~spl12_38),
% 0.20/0.52    inference(avatar_component_clause,[],[f274])).
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    ~spl12_22 | ~spl12_14 | spl12_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f284,f145,f116,f160])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl12_14 <=> sK5 = sK6),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    spl12_20 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (~spl12_14 | spl12_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f147,f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    sK5 = sK6 | ~spl12_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f116])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | spl12_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f145])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    spl12_30 | ~spl12_29 | ~spl12_31 | ~spl12_38),
% 0.20/0.52    inference(avatar_split_clause,[],[f282,f274,f228,f216,f222])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    spl12_30 <=> sP11(sK3,sK1,sK5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    sP11(sK3,sK1,sK5) | (~spl12_29 | ~spl12_31 | ~spl12_38)),
% 0.20/0.52    inference(resolution,[],[f278,f218])).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X0) | sP11(sK3,sK1,X0)) ) | (~spl12_31 | ~spl12_38)),
% 0.20/0.52    inference(resolution,[],[f276,f238])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(X5)) | ~m1_connsp_2(sK8(sK1,sK4,sK5),sK1,X6) | sP11(X5,sK1,X6)) ) | ~spl12_31),
% 0.20/0.52    inference(resolution,[],[f230,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP11(X3,X1,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48_D])).
% 0.20/0.52  fof(f48_D,plain,(
% 0.20/0.52    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP11(X3,X1,X6)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).
% 0.20/0.52  fof(f277,plain,(
% 0.20/0.52    spl12_38 | ~spl12_15 | ~spl12_27),
% 0.20/0.52    inference(avatar_split_clause,[],[f272,f204,f121,f274])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl12_15 <=> r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    spl12_27 <=> r1_tarski(sK8(sK1,sK4,sK5),sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) | (~spl12_15 | ~spl12_27)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f270])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) | r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) | (~spl12_15 | ~spl12_27)),
% 0.20/0.52    inference(resolution,[],[f268,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),u1_struct_0(sK3)) | r1_tarski(sK8(sK1,sK4,sK5),X0)) ) | (~spl12_15 | ~spl12_27)),
% 0.20/0.52    inference(resolution,[],[f266,f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r1_tarski(sK4,u1_struct_0(sK3)) | ~spl12_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f121])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(sK4,X1) | r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),X1) | r1_tarski(sK8(sK1,sK4,sK5),X0)) ) | ~spl12_27),
% 0.20/0.52    inference(resolution,[],[f208,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK9(sK8(sK1,sK4,sK5),X0),sK4) | r1_tarski(sK8(sK1,sK4,sK5),X0)) ) | ~spl12_27),
% 0.20/0.52    inference(resolution,[],[f206,f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    ( ! [X2,X3,X1] : (~r1_tarski(X1,X3) | r2_hidden(sK9(X1,X2),X3) | r1_tarski(X1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f41,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    r1_tarski(sK8(sK1,sK4,sK5),sK4) | ~spl12_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f204])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ~spl12_16 | spl12_31 | ~spl12_13 | ~spl12_26),
% 0.20/0.52    inference(avatar_split_clause,[],[f226,f199,f111,f228,f126])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    spl12_16 <=> r2_hidden(sK5,sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    spl12_26 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    m1_subset_1(sK8(sK1,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK5,sK4) | (~spl12_13 | ~spl12_26)),
% 0.20/0.52    inference(resolution,[],[f200,f113])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl12_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f111])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(X0,sK4)) ) | ~spl12_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f199])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    ~spl12_30 | spl12_19 | spl12_3 | ~spl12_21 | ~spl12_13 | ~spl12_10 | spl12_11 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_4 | ~spl12_5 | spl12_6 | ~spl12_1 | ~spl12_2 | ~spl12_22),
% 0.20/0.52    inference(avatar_split_clause,[],[f220,f160,f56,f51,f76,f71,f66,f91,f86,f81,f101,f96,f111,f152,f61,f141,f222])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl12_3 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl12_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    spl12_8 <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl12_9 <=> v1_funct_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl12_4 <=> l1_pre_topc(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl12_5 <=> v2_pre_topc(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl12_6 <=> v2_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl12_1 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl12_2 <=> v2_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK5) | ~sP11(sK3,sK1,sK5) | ~spl12_22),
% 0.20/0.52    inference(resolution,[],[f49,f162])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl12_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f160])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X6) | ~sP11(X3,X1,X6)) )),
% 0.20/0.52    inference(general_splitting,[],[f45,f48_D])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.52    inference(equality_resolution,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.52  fof(f219,plain,(
% 0.20/0.52    ~spl12_16 | spl12_29 | ~spl12_13 | ~spl12_25),
% 0.20/0.52    inference(avatar_split_clause,[],[f214,f193,f111,f216,f126])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl12_25 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0) | ~r2_hidden(X0,sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5) | ~r2_hidden(sK5,sK4) | (~spl12_13 | ~spl12_25)),
% 0.20/0.52    inference(resolution,[],[f194,f113])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0) | ~r2_hidden(X0,sK4)) ) | ~spl12_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f193])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    spl12_28 | spl12_3 | ~spl12_8 | ~spl12_9 | ~spl12_4 | ~spl12_5 | spl12_6 | ~spl12_1 | ~spl12_2 | ~spl12_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f209,f81,f56,f51,f76,f71,f66,f91,f86,f61,f211])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),X1) | ~r1_tmap_1(sK1,sK0,sK2,X1) | ~sP10(X0,sK1,X1)) ) | ~spl12_7),
% 0.20/0.52    inference(resolution,[],[f47,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl12_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X6,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~sP10(X3,X1,X6)) )),
% 0.20/0.52    inference(general_splitting,[],[f44,f46_D])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    ~spl12_16 | spl12_27 | ~spl12_13 | ~spl12_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f202,f187,f111,f204,f126])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    spl12_24 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(sK8(sK1,sK4,X0),sK4) | ~r2_hidden(X0,sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    r1_tarski(sK8(sK1,sK4,sK5),sK4) | ~r2_hidden(sK5,sK4) | (~spl12_13 | ~spl12_24)),
% 0.20/0.52    inference(resolution,[],[f188,f113])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(sK8(sK1,sK4,X0),sK4) | ~r2_hidden(X0,sK4)) ) | ~spl12_24),
% 0.20/0.52    inference(avatar_component_clause,[],[f187])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    ~spl12_17 | spl12_26 | spl12_6 | ~spl12_4 | ~spl12_5 | ~spl12_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f197,f106,f71,f66,f76,f199,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    spl12_17 <=> v3_pre_topc(sK4,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    spl12_12 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,sK4) | m1_subset_1(sK8(sK1,sK4,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(sK4,sK1)) ) | ~spl12_12),
% 0.20/0.52    inference(resolution,[],[f34,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl12_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f106])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ~spl12_17 | spl12_25 | spl12_6 | ~spl12_4 | ~spl12_5 | ~spl12_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f191,f106,f71,f66,f76,f193,f131])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,sK4) | m1_connsp_2(sK8(sK1,sK4,X0),sK1,X0) | ~v3_pre_topc(sK4,sK1)) ) | ~spl12_12),
% 0.20/0.52    inference(resolution,[],[f35,f108])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | m1_connsp_2(sK8(X0,X1,X2),X0,X2) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ~spl12_17 | spl12_24 | spl12_6 | ~spl12_4 | ~spl12_5 | ~spl12_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f185,f106,f71,f66,f76,f187,f131])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,sK4) | r1_tarski(sK8(sK1,sK4,X0),sK4) | ~v3_pre_topc(sK4,sK1)) ) | ~spl12_12),
% 0.20/0.52    inference(resolution,[],[f36,f108])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_tarski(sK8(X0,X1,X2),X1) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    spl12_22 | ~spl12_14 | ~spl12_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f158,f145,f116,f160])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | (~spl12_14 | ~spl12_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f146,f118])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~spl12_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f145])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl12_21 | ~spl12_14 | ~spl12_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f150,f136,f116,f152])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    spl12_18 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl12_14 | ~spl12_18)),
% 0.20/0.52    inference(forward_demodulation,[],[f138,f118])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    m1_subset_1(sK6,u1_struct_0(sK3)) | ~spl12_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f136])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    spl12_19 | spl12_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f13,f145,f141])).
% 0.20/0.53  % (24447)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f6])).
% 0.20/0.53  fof(f6,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f4])).
% 0.20/0.53  fof(f4,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ~spl12_19 | ~spl12_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f14,f145,f141])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    spl12_18),
% 0.20/0.53    inference(avatar_split_clause,[],[f15,f136])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    spl12_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f16,f131])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    v3_pre_topc(sK4,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl12_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f17,f126])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    r2_hidden(sK5,sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    spl12_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f18,f121])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    spl12_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f19,f116])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    sK5 = sK6),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl12_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f20,f111])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl12_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f21,f106])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ~spl12_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f22,f101])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ~v2_struct_0(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl12_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f23,f96])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    m1_pre_topc(sK3,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl12_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f24,f91])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl12_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f86])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl12_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f81])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ~spl12_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f27,f76])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl12_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f28,f71])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    v2_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    spl12_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f29,f66])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    l1_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~spl12_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f30,f61])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    spl12_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f31,f56])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    spl12_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f32,f51])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (24451)------------------------------
% 0.20/0.53  % (24451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24451)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (24451)Memory used [KB]: 11001
% 0.20/0.53  % (24451)Time elapsed: 0.115 s
% 0.20/0.53  % (24451)------------------------------
% 0.20/0.53  % (24451)------------------------------
% 0.20/0.53  % (24441)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (24434)Success in time 0.174 s
%------------------------------------------------------------------------------
