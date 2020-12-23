%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 316 expanded)
%              Number of leaves         :   37 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  633 (2001 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f112,f117,f122,f131,f139,f158,f164,f170,f199,f213,f244,f256,f265,f291,f306])).

fof(f306,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_21
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_21
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f297,f304])).

fof(f304,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_24
    | ~ spl4_26
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f303,f264])).

fof(f264,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl4_26
  <=> sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f303,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f302,f290])).

fof(f290,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_29
  <=> u1_struct_0(sK2) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f302,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f294,f250])).

fof(f250,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f249,f150])).

fof(f150,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f111,f130,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f249,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f76,f81,f86,f91,f96,f101,f116,f116,f121,f130,f243,f159])).

fof(f159,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | k3_tmap_1(X3,X2,X1,X0,sK3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl4_8 ),
    inference(resolution,[],[f60,f111])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f243,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl4_24
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f121,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_10
  <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f116,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f96,plain,
    ( v2_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f76,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f294,plain,
    ( ~ r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | spl4_12
    | ~ spl4_29 ),
    inference(superposition,[],[f138,f290])).

fof(f138,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_12
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f297,plain,
    ( r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3)
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(superposition,[],[f212,f290])).

fof(f212,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_21
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f291,plain,
    ( spl4_29
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f257,f253,f196,f167,f288])).

fof(f167,plain,
    ( spl4_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f196,plain,
    ( spl4_20
  <=> v4_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f253,plain,
    ( spl4_25
  <=> v1_partfun1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f257,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f169,f198,f255,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f255,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f253])).

fof(f198,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f169,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f265,plain,
    ( spl4_26
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f175,f167,f262])).

fof(f175,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f169,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f256,plain,
    ( spl4_25
    | spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f219,f155,f128,f119,f109,f89,f253])).

fof(f155,plain,
    ( spl4_14
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f219,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f218,f171])).

fof(f171,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl4_4
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f91,f157,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f157,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f218,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f217,f121])).

fof(f217,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f149,f130])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_partfun1(sK3,X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f62,f111])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f244,plain,
    ( spl4_24
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f172,f161,f241])).

fof(f161,plain,
    ( spl4_15
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f172,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f163,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f163,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f213,plain,
    ( spl4_21
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f152,f128,f119,f109,f210])).

fof(f152,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f111,f121,f130,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f199,plain,
    ( spl4_20
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f147,f128,f196])).

fof(f147,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f170,plain,
    ( spl4_16
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f145,f128,f167])).

fof(f145,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f130,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f164,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f132,f114,f84,f161])).

fof(f132,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f116,f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f158,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f124,f99,f155])).

fof(f124,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f139,plain,(
    ~ spl4_12 ),
    inference(avatar_split_clause,[],[f54,f136])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
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
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
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
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f131,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f53,f128])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f122,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:51:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (812875776)
% 0.15/0.37  ipcrm: permission denied for id (816480259)
% 0.15/0.37  ipcrm: permission denied for id (816513028)
% 0.21/0.38  ipcrm: permission denied for id (816611335)
% 0.21/0.38  ipcrm: permission denied for id (816676873)
% 0.21/0.38  ipcrm: permission denied for id (813137930)
% 0.21/0.38  ipcrm: permission denied for id (813203468)
% 0.21/0.39  ipcrm: permission denied for id (816742413)
% 0.21/0.39  ipcrm: permission denied for id (813269006)
% 0.21/0.39  ipcrm: permission denied for id (816775183)
% 0.21/0.39  ipcrm: permission denied for id (813334544)
% 0.21/0.39  ipcrm: permission denied for id (813367313)
% 0.21/0.39  ipcrm: permission denied for id (816807954)
% 0.21/0.39  ipcrm: permission denied for id (813432852)
% 0.21/0.40  ipcrm: permission denied for id (813563928)
% 0.21/0.40  ipcrm: permission denied for id (813596697)
% 0.21/0.40  ipcrm: permission denied for id (813629466)
% 0.21/0.40  ipcrm: permission denied for id (813662235)
% 0.21/0.41  ipcrm: permission denied for id (813727774)
% 0.21/0.41  ipcrm: permission denied for id (813760543)
% 0.21/0.41  ipcrm: permission denied for id (813793313)
% 0.21/0.41  ipcrm: permission denied for id (817070114)
% 0.21/0.41  ipcrm: permission denied for id (817135652)
% 0.21/0.42  ipcrm: permission denied for id (817201190)
% 0.21/0.42  ipcrm: permission denied for id (814022697)
% 0.21/0.42  ipcrm: permission denied for id (817332267)
% 0.21/0.42  ipcrm: permission denied for id (817365036)
% 0.21/0.43  ipcrm: permission denied for id (814153774)
% 0.21/0.43  ipcrm: permission denied for id (814186543)
% 0.21/0.43  ipcrm: permission denied for id (817430576)
% 0.21/0.43  ipcrm: permission denied for id (814219313)
% 0.21/0.43  ipcrm: permission denied for id (817463346)
% 0.21/0.43  ipcrm: permission denied for id (814252083)
% 0.21/0.43  ipcrm: permission denied for id (817496116)
% 0.21/0.44  ipcrm: permission denied for id (817561654)
% 0.21/0.44  ipcrm: permission denied for id (814383159)
% 0.21/0.44  ipcrm: permission denied for id (814448697)
% 0.21/0.44  ipcrm: permission denied for id (817627194)
% 0.21/0.44  ipcrm: permission denied for id (814514236)
% 0.21/0.45  ipcrm: permission denied for id (814612544)
% 0.21/0.45  ipcrm: permission denied for id (814710851)
% 0.21/0.45  ipcrm: permission denied for id (814776389)
% 0.21/0.46  ipcrm: permission denied for id (814809158)
% 0.21/0.46  ipcrm: permission denied for id (817954888)
% 0.21/0.46  ipcrm: permission denied for id (817987657)
% 0.21/0.46  ipcrm: permission denied for id (814940235)
% 0.21/0.46  ipcrm: permission denied for id (814973004)
% 0.21/0.46  ipcrm: permission denied for id (815005773)
% 0.21/0.47  ipcrm: permission denied for id (818118736)
% 0.21/0.47  ipcrm: permission denied for id (815104082)
% 0.21/0.47  ipcrm: permission denied for id (815169619)
% 0.21/0.47  ipcrm: permission denied for id (818184276)
% 0.21/0.47  ipcrm: permission denied for id (818217045)
% 0.21/0.48  ipcrm: permission denied for id (815267926)
% 0.21/0.48  ipcrm: permission denied for id (818249815)
% 0.21/0.48  ipcrm: permission denied for id (818380891)
% 0.21/0.48  ipcrm: permission denied for id (815399004)
% 0.21/0.48  ipcrm: permission denied for id (818413661)
% 0.21/0.49  ipcrm: permission denied for id (815464542)
% 0.21/0.49  ipcrm: permission denied for id (815497311)
% 0.21/0.49  ipcrm: permission denied for id (818446432)
% 0.21/0.49  ipcrm: permission denied for id (818479201)
% 0.21/0.49  ipcrm: permission denied for id (815628386)
% 0.21/0.49  ipcrm: permission denied for id (818511971)
% 0.21/0.49  ipcrm: permission denied for id (815693924)
% 0.21/0.50  ipcrm: permission denied for id (815726694)
% 0.21/0.50  ipcrm: permission denied for id (818577511)
% 0.21/0.50  ipcrm: permission denied for id (815759464)
% 0.21/0.50  ipcrm: permission denied for id (818610281)
% 0.21/0.50  ipcrm: permission denied for id (815825002)
% 0.21/0.50  ipcrm: permission denied for id (815857771)
% 0.21/0.50  ipcrm: permission denied for id (818643052)
% 0.21/0.51  ipcrm: permission denied for id (818675821)
% 0.21/0.51  ipcrm: permission denied for id (815890542)
% 0.21/0.51  ipcrm: permission denied for id (816021619)
% 0.21/0.52  ipcrm: permission denied for id (816054388)
% 0.21/0.52  ipcrm: permission denied for id (816119926)
% 0.21/0.52  ipcrm: permission denied for id (818937976)
% 0.21/0.52  ipcrm: permission denied for id (816218234)
% 0.21/0.53  ipcrm: permission denied for id (819036284)
% 0.21/0.53  ipcrm: permission denied for id (819069053)
% 0.21/0.53  ipcrm: permission denied for id (816382079)
% 0.38/0.63  % (12873)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.38/0.65  % (12891)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.38/0.65  % (12873)Refutation not found, incomplete strategy% (12873)------------------------------
% 0.38/0.65  % (12873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.65  % (12873)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.65  
% 0.38/0.65  % (12873)Memory used [KB]: 10746
% 0.38/0.65  % (12873)Time elapsed: 0.085 s
% 0.38/0.65  % (12873)------------------------------
% 0.38/0.65  % (12873)------------------------------
% 0.38/0.66  % (12882)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.38/0.66  % (12881)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.38/0.66  % (12885)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.38/0.66  % (12891)Refutation found. Thanks to Tanya!
% 0.38/0.66  % SZS status Theorem for theBenchmark
% 0.38/0.67  % SZS output start Proof for theBenchmark
% 0.38/0.67  fof(f309,plain,(
% 0.38/0.67    $false),
% 0.38/0.67    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f112,f117,f122,f131,f139,f158,f164,f170,f199,f213,f244,f256,f265,f291,f306])).
% 0.38/0.67  fof(f306,plain,(
% 0.38/0.67    spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_21 | ~spl4_24 | ~spl4_26 | ~spl4_29),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f305])).
% 0.38/0.67  fof(f305,plain,(
% 0.38/0.67    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_21 | ~spl4_24 | ~spl4_26 | ~spl4_29)),
% 0.38/0.67    inference(subsumption_resolution,[],[f297,f304])).
% 0.38/0.67  fof(f304,plain,(
% 0.38/0.67    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_24 | ~spl4_26 | ~spl4_29)),
% 0.38/0.67    inference(forward_demodulation,[],[f303,f264])).
% 0.38/0.67  fof(f264,plain,(
% 0.38/0.67    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl4_26),
% 0.38/0.67    inference(avatar_component_clause,[],[f262])).
% 0.38/0.67  fof(f262,plain,(
% 0.38/0.67    spl4_26 <=> sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.38/0.67  fof(f303,plain,(
% 0.38/0.67    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k7_relat_1(sK3,k1_relat_1(sK3))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_24 | ~spl4_29)),
% 0.38/0.67    inference(forward_demodulation,[],[f302,f290])).
% 0.38/0.67  fof(f290,plain,(
% 0.38/0.67    u1_struct_0(sK2) = k1_relat_1(sK3) | ~spl4_29),
% 0.38/0.67    inference(avatar_component_clause,[],[f288])).
% 0.38/0.67  fof(f288,plain,(
% 0.38/0.67    spl4_29 <=> u1_struct_0(sK2) = k1_relat_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.38/0.67  fof(f302,plain,(
% 0.38/0.67    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_24 | ~spl4_29)),
% 0.38/0.67    inference(forward_demodulation,[],[f294,f250])).
% 0.38/0.67  fof(f250,plain,(
% 0.38/0.67    k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k7_relat_1(sK3,u1_struct_0(sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_24)),
% 0.38/0.67    inference(forward_demodulation,[],[f249,f150])).
% 0.38/0.67  fof(f150,plain,(
% 0.38/0.67    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_8 | ~spl4_11)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f111,f130,f69])).
% 0.38/0.67  fof(f69,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f35])).
% 0.38/0.67  fof(f35,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.38/0.67    inference(flattening,[],[f34])).
% 0.38/0.67  fof(f34,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.38/0.67    inference(ennf_transformation,[],[f6])).
% 0.38/0.67  fof(f6,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.38/0.67  fof(f130,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl4_11),
% 0.38/0.67    inference(avatar_component_clause,[],[f128])).
% 0.38/0.67  fof(f128,plain,(
% 0.38/0.67    spl4_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.38/0.67  fof(f111,plain,(
% 0.38/0.67    v1_funct_1(sK3) | ~spl4_8),
% 0.38/0.67    inference(avatar_component_clause,[],[f109])).
% 0.38/0.67  fof(f109,plain,(
% 0.38/0.67    spl4_8 <=> v1_funct_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.38/0.67  fof(f249,plain,(
% 0.38/0.67    k3_tmap_1(sK0,sK1,sK2,sK2,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_24)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f76,f81,f86,f91,f96,f101,f116,f116,f121,f130,f243,f159])).
% 0.38/0.67  fof(f159,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X3,X2,X1,X0,sK3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK3,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl4_8),
% 0.38/0.67    inference(resolution,[],[f60,f111])).
% 0.38/0.67  fof(f60,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f25])).
% 0.38/0.67  fof(f25,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.38/0.67    inference(flattening,[],[f24])).
% 0.38/0.67  fof(f24,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f11])).
% 0.38/0.67  fof(f11,axiom,(
% 0.38/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.38/0.67  fof(f243,plain,(
% 0.38/0.67    m1_pre_topc(sK2,sK2) | ~spl4_24),
% 0.38/0.67    inference(avatar_component_clause,[],[f241])).
% 0.38/0.67  fof(f241,plain,(
% 0.38/0.67    spl4_24 <=> m1_pre_topc(sK2,sK2)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.38/0.67  fof(f121,plain,(
% 0.38/0.67    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl4_10),
% 0.38/0.67    inference(avatar_component_clause,[],[f119])).
% 0.38/0.67  fof(f119,plain,(
% 0.38/0.67    spl4_10 <=> v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.38/0.67  fof(f116,plain,(
% 0.38/0.67    m1_pre_topc(sK2,sK0) | ~spl4_9),
% 0.38/0.67    inference(avatar_component_clause,[],[f114])).
% 0.38/0.67  fof(f114,plain,(
% 0.38/0.67    spl4_9 <=> m1_pre_topc(sK2,sK0)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.38/0.67  fof(f101,plain,(
% 0.38/0.67    l1_pre_topc(sK1) | ~spl4_6),
% 0.38/0.67    inference(avatar_component_clause,[],[f99])).
% 0.38/0.67  fof(f99,plain,(
% 0.38/0.67    spl4_6 <=> l1_pre_topc(sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.38/0.67  fof(f96,plain,(
% 0.38/0.67    v2_pre_topc(sK1) | ~spl4_5),
% 0.38/0.67    inference(avatar_component_clause,[],[f94])).
% 0.38/0.67  fof(f94,plain,(
% 0.38/0.67    spl4_5 <=> v2_pre_topc(sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.38/0.67  fof(f91,plain,(
% 0.38/0.67    ~v2_struct_0(sK1) | spl4_4),
% 0.38/0.67    inference(avatar_component_clause,[],[f89])).
% 0.38/0.67  fof(f89,plain,(
% 0.38/0.67    spl4_4 <=> v2_struct_0(sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.38/0.67  fof(f86,plain,(
% 0.38/0.67    l1_pre_topc(sK0) | ~spl4_3),
% 0.38/0.67    inference(avatar_component_clause,[],[f84])).
% 0.38/0.67  fof(f84,plain,(
% 0.38/0.67    spl4_3 <=> l1_pre_topc(sK0)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.38/0.67  fof(f81,plain,(
% 0.38/0.67    v2_pre_topc(sK0) | ~spl4_2),
% 0.38/0.67    inference(avatar_component_clause,[],[f79])).
% 0.38/0.67  fof(f79,plain,(
% 0.38/0.67    spl4_2 <=> v2_pre_topc(sK0)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.38/0.67  fof(f76,plain,(
% 0.38/0.67    ~v2_struct_0(sK0) | spl4_1),
% 0.38/0.67    inference(avatar_component_clause,[],[f74])).
% 0.38/0.67  fof(f74,plain,(
% 0.38/0.67    spl4_1 <=> v2_struct_0(sK0)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.38/0.67  fof(f294,plain,(
% 0.38/0.67    ~r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) | (spl4_12 | ~spl4_29)),
% 0.38/0.67    inference(superposition,[],[f138,f290])).
% 0.38/0.67  fof(f138,plain,(
% 0.38/0.67    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) | spl4_12),
% 0.38/0.67    inference(avatar_component_clause,[],[f136])).
% 0.38/0.67  fof(f136,plain,(
% 0.38/0.67    spl4_12 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.38/0.67  fof(f297,plain,(
% 0.38/0.67    r2_funct_2(k1_relat_1(sK3),u1_struct_0(sK1),sK3,sK3) | (~spl4_21 | ~spl4_29)),
% 0.38/0.67    inference(superposition,[],[f212,f290])).
% 0.38/0.67  fof(f212,plain,(
% 0.38/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) | ~spl4_21),
% 0.38/0.67    inference(avatar_component_clause,[],[f210])).
% 0.38/0.67  fof(f210,plain,(
% 0.38/0.67    spl4_21 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.38/0.67  fof(f291,plain,(
% 0.38/0.67    spl4_29 | ~spl4_16 | ~spl4_20 | ~spl4_25),
% 0.38/0.67    inference(avatar_split_clause,[],[f257,f253,f196,f167,f288])).
% 0.38/0.67  fof(f167,plain,(
% 0.38/0.67    spl4_16 <=> v1_relat_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.38/0.67  fof(f196,plain,(
% 0.38/0.67    spl4_20 <=> v4_relat_1(sK3,u1_struct_0(sK2))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.38/0.67  fof(f253,plain,(
% 0.38/0.67    spl4_25 <=> v1_partfun1(sK3,u1_struct_0(sK2))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.38/0.67  fof(f257,plain,(
% 0.38/0.67    u1_struct_0(sK2) = k1_relat_1(sK3) | (~spl4_16 | ~spl4_20 | ~spl4_25)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f169,f198,f255,f63])).
% 0.38/0.67  fof(f63,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.38/0.67    inference(cnf_transformation,[],[f41])).
% 0.38/0.67  fof(f41,plain,(
% 0.38/0.67    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.38/0.67    inference(nnf_transformation,[],[f29])).
% 0.38/0.67  fof(f29,plain,(
% 0.38/0.67    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.38/0.67    inference(flattening,[],[f28])).
% 0.38/0.67  fof(f28,plain,(
% 0.38/0.67    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.38/0.67    inference(ennf_transformation,[],[f5])).
% 0.38/0.67  fof(f5,axiom,(
% 0.38/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.38/0.67  fof(f255,plain,(
% 0.38/0.67    v1_partfun1(sK3,u1_struct_0(sK2)) | ~spl4_25),
% 0.38/0.67    inference(avatar_component_clause,[],[f253])).
% 0.38/0.67  fof(f198,plain,(
% 0.38/0.67    v4_relat_1(sK3,u1_struct_0(sK2)) | ~spl4_20),
% 0.38/0.67    inference(avatar_component_clause,[],[f196])).
% 0.38/0.67  fof(f169,plain,(
% 0.38/0.67    v1_relat_1(sK3) | ~spl4_16),
% 0.38/0.67    inference(avatar_component_clause,[],[f167])).
% 0.38/0.67  fof(f265,plain,(
% 0.38/0.67    spl4_26 | ~spl4_16),
% 0.38/0.67    inference(avatar_split_clause,[],[f175,f167,f262])).
% 0.38/0.67  fof(f175,plain,(
% 0.38/0.67    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~spl4_16),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f169,f55])).
% 0.38/0.67  fof(f55,plain,(
% 0.38/0.67    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.38/0.67    inference(cnf_transformation,[],[f18])).
% 0.38/0.67  fof(f18,plain,(
% 0.38/0.67    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f1])).
% 0.38/0.67  fof(f1,axiom,(
% 0.38/0.67    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.38/0.67  fof(f256,plain,(
% 0.38/0.67    spl4_25 | spl4_4 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_14),
% 0.38/0.67    inference(avatar_split_clause,[],[f219,f155,f128,f119,f109,f89,f253])).
% 0.38/0.67  fof(f155,plain,(
% 0.38/0.67    spl4_14 <=> l1_struct_0(sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.38/0.67  fof(f219,plain,(
% 0.38/0.67    v1_partfun1(sK3,u1_struct_0(sK2)) | (spl4_4 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_14)),
% 0.38/0.67    inference(subsumption_resolution,[],[f218,f171])).
% 0.38/0.67  fof(f171,plain,(
% 0.38/0.67    ~v1_xboole_0(u1_struct_0(sK1)) | (spl4_4 | ~spl4_14)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f91,f157,f59])).
% 0.38/0.67  fof(f59,plain,(
% 0.38/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f23])).
% 0.38/0.67  fof(f23,plain,(
% 0.38/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.38/0.67    inference(flattening,[],[f22])).
% 0.38/0.67  fof(f22,plain,(
% 0.38/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f10])).
% 0.38/0.67  fof(f10,axiom,(
% 0.38/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.38/0.67  fof(f157,plain,(
% 0.38/0.67    l1_struct_0(sK1) | ~spl4_14),
% 0.38/0.67    inference(avatar_component_clause,[],[f155])).
% 0.38/0.67  fof(f218,plain,(
% 0.38/0.67    v1_partfun1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl4_8 | ~spl4_10 | ~spl4_11)),
% 0.38/0.67    inference(subsumption_resolution,[],[f217,f121])).
% 0.38/0.67  fof(f217,plain,(
% 0.38/0.67    v1_partfun1(sK3,u1_struct_0(sK2)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl4_8 | ~spl4_11)),
% 0.38/0.67    inference(resolution,[],[f149,f130])).
% 0.38/0.67  fof(f149,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK3,X0) | ~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X1)) ) | ~spl4_8),
% 0.38/0.67    inference(resolution,[],[f62,f111])).
% 0.38/0.67  fof(f62,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f27])).
% 0.38/0.67  fof(f27,plain,(
% 0.38/0.67    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.38/0.67    inference(flattening,[],[f26])).
% 0.38/0.67  fof(f26,plain,(
% 0.38/0.67    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.38/0.67    inference(ennf_transformation,[],[f4])).
% 0.38/0.67  fof(f4,axiom,(
% 0.38/0.67    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.38/0.67  fof(f244,plain,(
% 0.38/0.67    spl4_24 | ~spl4_15),
% 0.38/0.67    inference(avatar_split_clause,[],[f172,f161,f241])).
% 0.38/0.67  fof(f161,plain,(
% 0.38/0.67    spl4_15 <=> l1_pre_topc(sK2)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.38/0.67  fof(f172,plain,(
% 0.38/0.67    m1_pre_topc(sK2,sK2) | ~spl4_15),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f163,f57])).
% 0.38/0.67  fof(f57,plain,(
% 0.38/0.67    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f20])).
% 0.38/0.67  fof(f20,plain,(
% 0.38/0.67    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f12])).
% 0.38/0.67  fof(f12,axiom,(
% 0.38/0.67    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.38/0.67  fof(f163,plain,(
% 0.38/0.67    l1_pre_topc(sK2) | ~spl4_15),
% 0.38/0.67    inference(avatar_component_clause,[],[f161])).
% 0.38/0.67  fof(f213,plain,(
% 0.38/0.67    spl4_21 | ~spl4_8 | ~spl4_10 | ~spl4_11),
% 0.38/0.67    inference(avatar_split_clause,[],[f152,f128,f119,f109,f210])).
% 0.38/0.67  fof(f152,plain,(
% 0.38/0.67    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) | (~spl4_8 | ~spl4_10 | ~spl4_11)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f111,f121,f130,f72])).
% 0.38/0.67  fof(f72,plain,(
% 0.38/0.67    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.38/0.67    inference(duplicate_literal_removal,[],[f71])).
% 0.38/0.67  fof(f71,plain,(
% 0.38/0.67    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.38/0.67    inference(equality_resolution,[],[f68])).
% 0.38/0.67  fof(f68,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f42])).
% 0.38/0.67  fof(f42,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.38/0.67    inference(nnf_transformation,[],[f33])).
% 0.38/0.67  fof(f33,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.38/0.67    inference(flattening,[],[f32])).
% 0.38/0.67  fof(f32,plain,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.38/0.67    inference(ennf_transformation,[],[f7])).
% 0.38/0.67  fof(f7,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.38/0.67  fof(f199,plain,(
% 0.38/0.67    spl4_20 | ~spl4_11),
% 0.38/0.67    inference(avatar_split_clause,[],[f147,f128,f196])).
% 0.38/0.67  fof(f147,plain,(
% 0.38/0.67    v4_relat_1(sK3,u1_struct_0(sK2)) | ~spl4_11),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f130,f66])).
% 0.38/0.67  fof(f66,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f31])).
% 0.38/0.67  fof(f31,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f15])).
% 0.38/0.67  fof(f15,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.38/0.67    inference(pure_predicate_removal,[],[f3])).
% 0.38/0.67  fof(f3,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.38/0.67  fof(f170,plain,(
% 0.38/0.67    spl4_16 | ~spl4_11),
% 0.38/0.67    inference(avatar_split_clause,[],[f145,f128,f167])).
% 0.38/0.67  fof(f145,plain,(
% 0.38/0.67    v1_relat_1(sK3) | ~spl4_11),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f130,f65])).
% 0.38/0.67  fof(f65,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f30])).
% 0.38/0.67  fof(f30,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f2])).
% 0.38/0.67  fof(f2,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.38/0.67  fof(f164,plain,(
% 0.38/0.67    spl4_15 | ~spl4_3 | ~spl4_9),
% 0.38/0.67    inference(avatar_split_clause,[],[f132,f114,f84,f161])).
% 0.38/0.67  fof(f132,plain,(
% 0.38/0.67    l1_pre_topc(sK2) | (~spl4_3 | ~spl4_9)),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f116,f86,f58])).
% 0.38/0.67  fof(f58,plain,(
% 0.38/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f21])).
% 0.38/0.67  fof(f21,plain,(
% 0.38/0.67    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f9])).
% 0.38/0.67  fof(f9,axiom,(
% 0.38/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.38/0.67  fof(f158,plain,(
% 0.38/0.67    spl4_14 | ~spl4_6),
% 0.38/0.67    inference(avatar_split_clause,[],[f124,f99,f155])).
% 0.38/0.67  fof(f124,plain,(
% 0.38/0.67    l1_struct_0(sK1) | ~spl4_6),
% 0.38/0.67    inference(unit_resulting_resolution,[],[f101,f56])).
% 0.38/0.67  fof(f56,plain,(
% 0.38/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f19,plain,(
% 0.38/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.38/0.67    inference(ennf_transformation,[],[f8])).
% 0.38/0.67  fof(f8,axiom,(
% 0.38/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.38/0.67  fof(f139,plain,(
% 0.38/0.67    ~spl4_12),
% 0.38/0.67    inference(avatar_split_clause,[],[f54,f136])).
% 0.38/0.67  fof(f54,plain,(
% 0.38/0.67    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3))),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f40,plain,(
% 0.38/0.67    (((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.38/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f39,f38,f37,f36])).
% 0.38/0.67  fof(f36,plain,(
% 0.38/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f37,plain,(
% 0.38/0.67    ? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(sK0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f38,plain,(
% 0.38/0.67    ? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f39,plain,(
% 0.38/0.67    ? [X3] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X3,k3_tmap_1(sK0,sK1,sK2,sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(sK0,sK1,sK2,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.38/0.67    introduced(choice_axiom,[])).
% 0.38/0.67  fof(f17,plain,(
% 0.38/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.38/0.67    inference(flattening,[],[f16])).
% 0.38/0.67  fof(f16,plain,(
% 0.38/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f14])).
% 0.38/0.67  fof(f14,negated_conjecture,(
% 0.38/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.38/0.67    inference(negated_conjecture,[],[f13])).
% 0.38/0.67  fof(f13,conjecture,(
% 0.38/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 0.38/0.67  fof(f131,plain,(
% 0.38/0.67    spl4_11),
% 0.38/0.67    inference(avatar_split_clause,[],[f53,f128])).
% 0.38/0.67  fof(f53,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f122,plain,(
% 0.38/0.67    spl4_10),
% 0.38/0.67    inference(avatar_split_clause,[],[f52,f119])).
% 0.38/0.67  fof(f52,plain,(
% 0.38/0.67    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f117,plain,(
% 0.38/0.67    spl4_9),
% 0.38/0.67    inference(avatar_split_clause,[],[f50,f114])).
% 0.38/0.67  fof(f50,plain,(
% 0.38/0.67    m1_pre_topc(sK2,sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f112,plain,(
% 0.38/0.67    spl4_8),
% 0.38/0.67    inference(avatar_split_clause,[],[f51,f109])).
% 0.38/0.67  fof(f51,plain,(
% 0.38/0.67    v1_funct_1(sK3)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f102,plain,(
% 0.38/0.67    spl4_6),
% 0.38/0.67    inference(avatar_split_clause,[],[f48,f99])).
% 0.38/0.67  fof(f48,plain,(
% 0.38/0.67    l1_pre_topc(sK1)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f97,plain,(
% 0.38/0.67    spl4_5),
% 0.38/0.67    inference(avatar_split_clause,[],[f47,f94])).
% 0.38/0.67  fof(f47,plain,(
% 0.38/0.67    v2_pre_topc(sK1)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f92,plain,(
% 0.38/0.67    ~spl4_4),
% 0.38/0.67    inference(avatar_split_clause,[],[f46,f89])).
% 0.38/0.67  fof(f46,plain,(
% 0.38/0.67    ~v2_struct_0(sK1)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f87,plain,(
% 0.38/0.67    spl4_3),
% 0.38/0.67    inference(avatar_split_clause,[],[f45,f84])).
% 0.38/0.67  fof(f45,plain,(
% 0.38/0.67    l1_pre_topc(sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f82,plain,(
% 0.38/0.67    spl4_2),
% 0.38/0.67    inference(avatar_split_clause,[],[f44,f79])).
% 0.38/0.67  fof(f44,plain,(
% 0.38/0.67    v2_pre_topc(sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  fof(f77,plain,(
% 0.38/0.67    ~spl4_1),
% 0.38/0.67    inference(avatar_split_clause,[],[f43,f74])).
% 0.38/0.67  fof(f43,plain,(
% 0.38/0.67    ~v2_struct_0(sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f40])).
% 0.38/0.67  % SZS output end Proof for theBenchmark
% 0.38/0.67  % (12891)------------------------------
% 0.38/0.67  % (12891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (12891)Termination reason: Refutation
% 0.38/0.67  
% 0.38/0.67  % (12891)Memory used [KB]: 10874
% 0.38/0.67  % (12891)Time elapsed: 0.041 s
% 0.38/0.67  % (12891)------------------------------
% 0.38/0.67  % (12891)------------------------------
% 0.38/0.67  % (12707)Success in time 0.308 s
%------------------------------------------------------------------------------
