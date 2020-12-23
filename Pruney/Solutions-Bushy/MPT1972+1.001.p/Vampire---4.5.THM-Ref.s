%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1972+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  272 (1163 expanded)
%              Number of leaves         :   51 ( 595 expanded)
%              Depth                    :   10
%              Number of atoms          : 1537 (9048 expanded)
%              Number of equality atoms :   35 (  91 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f150,f151,f152,f153,f155,f156,f157,f158,f160,f161,f162,f163,f165,f166,f167,f168,f174,f179,f184,f189,f194,f199,f204,f216,f224,f229,f235,f242,f250,f256,f263,f271,f277,f284,f296,f319,f352,f358,f402,f407,f412,f417,f428,f528,f531,f542,f551,f553,f570,f583,f587,f588,f591,f592,f613,f629,f634])).

fof(f634,plain,
    ( ~ spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_41
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f633,f425,f409,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f126,f122,f118,f114,f293])).

fof(f293,plain,
    ( spl5_29
  <=> k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f114,plain,
    ( spl5_1
  <=> v2_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f118,plain,
    ( spl5_2
  <=> v13_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f122,plain,
    ( spl5_3
  <=> v2_waybel_7(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f126,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f130,plain,
    ( spl5_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f176,plain,
    ( spl5_10
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f181,plain,
    ( spl5_11
  <=> v2_lattice3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f186,plain,
    ( spl5_12
  <=> v1_lattice3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f191,plain,
    ( spl5_13
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f196,plain,
    ( spl5_14
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f201,plain,
    ( spl5_15
  <=> v3_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f226,plain,
    ( spl5_19
  <=> l1_orders_2(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f247,plain,
    ( spl5_22
  <=> v1_lattice3(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f268,plain,
    ( spl5_25
  <=> v2_lattice3(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f281,plain,
    ( spl5_27
  <=> v5_orders_2(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f316,plain,
    ( spl5_32
  <=> v4_orders_2(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f349,plain,
    ( spl5_35
  <=> v3_orders_2(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f409,plain,
    ( spl5_41
  <=> v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f425,plain,
    ( spl5_43
  <=> k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f633,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_41
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f632,f427])).

fof(f427,plain,
    ( k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f425])).

fof(f632,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_41 ),
    inference(unit_resulting_resolution,[],[f203,f198,f193,f188,f183,f178,f131,f115,f119,f123,f351,f318,f283,f249,f270,f228,f127,f410,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_7(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_7(X2,X1)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_7)).

fof(f410,plain,
    ( ~ v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f409])).

fof(f127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f228,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f270,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f268])).

fof(f249,plain,
    ( v1_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f247])).

fof(f283,plain,
    ( v5_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f281])).

fof(f318,plain,
    ( v4_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f316])).

fof(f351,plain,
    ( v3_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f349])).

fof(f123,plain,
    ( v2_waybel_7(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f119,plain,
    ( v13_waybel_0(sK3,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f115,plain,
    ( v2_waybel_0(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f131,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f178,plain,
    ( l1_orders_2(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f183,plain,
    ( v2_lattice3(sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f188,plain,
    ( v1_lattice3(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f186])).

fof(f193,plain,
    ( v5_orders_2(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f198,plain,
    ( v4_orders_2(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f203,plain,
    ( v3_orders_2(sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f201])).

fof(f629,plain,
    ( ~ spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_40
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f628,f425,f404,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f126,f122,f118,f114,f293])).

fof(f404,plain,
    ( spl5_40
  <=> v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f628,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_40
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f627,f427])).

fof(f627,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_40 ),
    inference(unit_resulting_resolution,[],[f203,f198,f193,f188,f183,f178,f131,f115,f119,f123,f351,f318,f283,f249,f270,f228,f127,f405,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_7(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X2,X1)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f405,plain,
    ( ~ v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | spl5_40 ),
    inference(avatar_component_clause,[],[f404])).

fof(f613,plain,
    ( ~ spl5_34
    | spl5_9 ),
    inference(avatar_split_clause,[],[f598,f146,f333])).

fof(f333,plain,
    ( spl5_34
  <=> sP0(k7_lattice3(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f146,plain,
    ( spl5_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f598,plain,
    ( ~ sP0(k7_lattice3(sK2),sK3)
    | spl5_9 ),
    inference(resolution,[],[f148,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(X1,X0)
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X1,X0)
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(X1,X0)
        | ~ v12_waybel_0(X1,X0)
        | ~ v1_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X1,X0)
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(X1,X0)
        & v12_waybel_0(X1,X0)
        & v1_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f592,plain,
    ( spl5_7
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f361,f333,f138])).

fof(f138,plain,
    ( spl5_7
  <=> v12_waybel_0(sK3,k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f361,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f335,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f335,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f333])).

fof(f591,plain,
    ( spl5_6
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f360,f333,f134])).

fof(f134,plain,
    ( spl5_6
  <=> v1_waybel_0(sK3,k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f360,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f335,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f588,plain,
    ( spl5_34
    | spl5_5
    | ~ spl5_36
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f525,f414,f409,f404,f399,f354,f130,f333])).

fof(f354,plain,
    ( spl5_36
  <=> sP1(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f399,plain,
    ( spl5_39
  <=> v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f414,plain,
    ( spl5_42
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f525,plain,
    ( sP0(k7_lattice3(sK2),sK3)
    | spl5_5
    | ~ spl5_36
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f131,f356,f401,f406,f411,f416,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f416,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f414])).

fof(f411,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f409])).

fof(f406,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f404])).

fof(f401,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f399])).

fof(f356,plain,
    ( sP1(k7_lattice3(sK2))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f354])).

fof(f587,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_34
    | ~ spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f564,f142,f146,f333,f138,f134,f130])).

fof(f142,plain,
    ( spl5_8
  <=> v1_waybel_7(sK3,k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f564,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | sP0(k7_lattice3(sK2),sK3)
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | v1_xboole_0(sK3)
    | ~ spl5_8 ),
    inference(resolution,[],[f143,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f143,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f583,plain,
    ( ~ spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f582,f425,f414,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f126,f122,f118,f114,f293])).

fof(f582,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_42
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f573,f427])).

fof(f573,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f203,f198,f193,f188,f183,f178,f131,f115,f119,f123,f351,f318,f283,f249,f270,f228,f127,f415,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f415,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f414])).

fof(f570,plain,
    ( ~ spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_39
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f569,f425,f399,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f126,f122,f118,f114,f293])).

fof(f569,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_39
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f568,f427])).

fof(f568,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f203,f198,f193,f188,f183,f178,f131,f115,f119,f123,f351,f318,f283,f249,f270,f228,f127,f400,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_7(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X2,X1)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f400,plain,
    ( ~ v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f399])).

fof(f553,plain,
    ( spl5_8
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f362,f333,f142])).

fof(f362,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f335,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f551,plain,
    ( ~ spl5_29
    | spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f550,f425,f414,f409,f404,f399,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f122,f293])).

fof(f550,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f549,f427])).

fof(f549,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | spl5_3
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f198,f193,f188,f183,f178,f131,f203,f351,f318,f283,f249,f270,f228,f411,f401,f406,f416,f124,f106])).

fof(f124,plain,
    ( ~ v2_waybel_7(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f542,plain,
    ( ~ spl5_29
    | spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f541,f425,f414,f409,f404,f399,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f126,f293])).

fof(f541,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f532,f427])).

fof(f532,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | spl5_4
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f198,f193,f188,f183,f178,f131,f203,f351,f318,f283,f249,f270,f228,f411,f401,f406,f416,f128,f107])).

fof(f128,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f531,plain,
    ( ~ spl5_29
    | spl5_2
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f530,f425,f414,f409,f404,f399,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f118,f293])).

fof(f530,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | spl5_2
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f529,f427])).

fof(f529,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | spl5_2
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f198,f193,f188,f183,f178,f131,f203,f351,f318,f283,f249,f270,f228,f411,f401,f406,f416,f120,f105])).

fof(f120,plain,
    ( ~ v13_waybel_0(sK3,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f528,plain,
    ( ~ spl5_29
    | spl5_1
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f527,f425,f414,f409,f404,f399,f349,f316,f281,f268,f247,f226,f201,f196,f191,f186,f181,f176,f130,f114,f293])).

fof(f527,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | spl5_1
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f526,f427])).

fof(f526,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | spl5_1
    | spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_22
    | ~ spl5_25
    | ~ spl5_27
    | ~ spl5_32
    | ~ spl5_35
    | ~ spl5_39
    | ~ spl5_40
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f193,f188,f183,f178,f203,f198,f116,f131,f351,f318,f283,f249,f270,f228,f411,f401,f406,f416,f104])).

fof(f116,plain,
    ( ~ v2_waybel_0(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f428,plain,
    ( spl5_43
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f421,f226,f221,f425])).

fof(f221,plain,
    ( spl5_18
  <=> v1_orders_2(k7_lattice3(k7_lattice3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f421,plain,
    ( k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK2))),u1_orders_2(k7_lattice3(k7_lattice3(sK2))))
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f223,f228,f108])).

fof(f108,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f223,plain,
    ( v1_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f417,plain,
    ( spl5_42
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f387,f354,f333,f414])).

fof(f387,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK2)))))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f335,f356,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0)))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f412,plain,
    ( spl5_41
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f388,f354,f333,f409])).

fof(f388,plain,
    ( v2_waybel_7(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f335,f356,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | v2_waybel_7(X1,k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f407,plain,
    ( spl5_40
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f389,f354,f333,f404])).

fof(f389,plain,
    ( v13_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f335,f356,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | v13_waybel_0(X1,k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f402,plain,
    ( spl5_39
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f390,f354,f333,f399])).

fof(f390,plain,
    ( v2_waybel_0(sK3,k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f335,f356,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | v2_waybel_0(X1,k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f358,plain,
    ( spl5_36
    | ~ spl5_24
    | ~ spl5_23
    | ~ spl5_21
    | ~ spl5_20
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f347,f274,f213,f232,f239,f253,f260,f354])).

fof(f260,plain,
    ( spl5_24
  <=> v4_orders_2(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f253,plain,
    ( spl5_23
  <=> v5_orders_2(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f239,plain,
    ( spl5_21
  <=> v1_lattice3(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f232,plain,
    ( spl5_20
  <=> v2_lattice3(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f213,plain,
    ( spl5_17
  <=> l1_orders_2(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f274,plain,
    ( spl5_26
  <=> v3_orders_2(k7_lattice3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f347,plain,
    ( ~ l1_orders_2(k7_lattice3(sK2))
    | ~ v2_lattice3(k7_lattice3(sK2))
    | ~ v1_lattice3(k7_lattice3(sK2))
    | ~ v5_orders_2(k7_lattice3(sK2))
    | ~ v4_orders_2(k7_lattice3(sK2))
    | sP1(k7_lattice3(sK2))
    | ~ spl5_26 ),
    inference(resolution,[],[f276,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f34,f33])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_7)).

fof(f276,plain,
    ( v3_orders_2(k7_lattice3(sK2))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f352,plain,
    ( spl5_35
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f346,f274,f213,f349])).

fof(f346,plain,
    ( v3_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f215,f276,f99])).

fof(f99,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(f215,plain,
    ( l1_orders_2(k7_lattice3(sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f213])).

fof(f319,plain,
    ( spl5_32
    | ~ spl5_17
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f313,f260,f213,f316])).

fof(f313,plain,
    ( v4_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f215,f262,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(f262,plain,
    ( v4_orders_2(k7_lattice3(sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f296,plain,
    ( spl5_29
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f285,f176,f293])).

fof(f285,plain,
    ( k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f178,f102])).

fof(f102,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(f284,plain,
    ( spl5_27
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f278,f253,f213,f281])).

fof(f278,plain,
    ( v5_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f215,f255,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(f255,plain,
    ( v5_orders_2(k7_lattice3(sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f253])).

fof(f277,plain,
    ( spl5_26
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f272,f201,f176,f274])).

fof(f272,plain,
    ( v3_orders_2(k7_lattice3(sK2))
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f203,f178,f99])).

fof(f271,plain,
    ( spl5_25
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f265,f239,f213,f268])).

fof(f265,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f215,f241,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_7)).

fof(f241,plain,
    ( v1_lattice3(k7_lattice3(sK2))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f239])).

fof(f263,plain,
    ( spl5_24
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f258,f196,f176,f260])).

fof(f258,plain,
    ( v4_orders_2(k7_lattice3(sK2))
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f198,f178,f97])).

fof(f256,plain,
    ( spl5_23
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f251,f191,f176,f253])).

fof(f251,plain,
    ( v5_orders_2(k7_lattice3(sK2))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f193,f178,f95])).

fof(f250,plain,
    ( spl5_22
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f244,f232,f213,f247])).

fof(f244,plain,
    ( v1_lattice3(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f215,f234,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(f234,plain,
    ( v2_lattice3(k7_lattice3(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f242,plain,
    ( spl5_21
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f237,f181,f176,f239])).

fof(f237,plain,
    ( v1_lattice3(k7_lattice3(sK2))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f183,f178,f93])).

fof(f235,plain,
    ( spl5_20
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f230,f186,f176,f232])).

fof(f230,plain,
    ( v2_lattice3(k7_lattice3(sK2))
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f188,f178,f91])).

fof(f229,plain,
    ( spl5_19
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f218,f213,f226])).

fof(f218,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f215,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f224,plain,
    ( spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f219,f213,f221])).

fof(f219,plain,
    ( v1_orders_2(k7_lattice3(k7_lattice3(sK2)))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f215,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f216,plain,
    ( spl5_17
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f211,f176,f213])).

fof(f211,plain,
    ( l1_orders_2(k7_lattice3(sK2))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f178,f101])).

fof(f204,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f45,f201])).

fof(f45,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
      | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
      | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
      | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_waybel_7(sK3,sK2)
      | ~ v13_waybel_0(sK3,sK2)
      | ~ v2_waybel_0(sK3,sK2)
      | v1_xboole_0(sK3) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
        & v1_waybel_7(sK3,k7_lattice3(sK2))
        & v12_waybel_0(sK3,k7_lattice3(sK2))
        & v1_waybel_0(sK3,k7_lattice3(sK2))
        & ~ v1_xboole_0(sK3) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        & v2_waybel_7(sK3,sK2)
        & v13_waybel_0(sK3,sK2)
        & v2_waybel_0(sK3,sK2)
        & ~ v1_xboole_0(sK3) ) )
    & l1_orders_2(sK2)
    & v2_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v1_waybel_7(X1,k7_lattice3(X0))
              | ~ v12_waybel_0(X1,k7_lattice3(X0))
              | ~ v1_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X1,X0)
              | ~ v13_waybel_0(X1,X0)
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v1_waybel_7(X1,k7_lattice3(X0))
                & v12_waybel_0(X1,k7_lattice3(X0))
                & v1_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_waybel_7(X1,X0)
                & v13_waybel_0(X1,X0)
                & v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
            | ~ v1_waybel_7(X1,k7_lattice3(sK2))
            | ~ v12_waybel_0(X1,k7_lattice3(sK2))
            | ~ v1_waybel_0(X1,k7_lattice3(sK2))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v2_waybel_7(X1,sK2)
            | ~ v13_waybel_0(X1,sK2)
            | ~ v2_waybel_0(X1,sK2)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
              & v1_waybel_7(X1,k7_lattice3(sK2))
              & v12_waybel_0(X1,k7_lattice3(sK2))
              & v1_waybel_0(X1,k7_lattice3(sK2))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
              & v2_waybel_7(X1,sK2)
              & v13_waybel_0(X1,sK2)
              & v2_waybel_0(X1,sK2)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK2)
      & v2_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
          | ~ v1_waybel_7(X1,k7_lattice3(sK2))
          | ~ v12_waybel_0(X1,k7_lattice3(sK2))
          | ~ v1_waybel_0(X1,k7_lattice3(sK2))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v2_waybel_7(X1,sK2)
          | ~ v13_waybel_0(X1,sK2)
          | ~ v2_waybel_0(X1,sK2)
          | v1_xboole_0(X1) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
            & v1_waybel_7(X1,k7_lattice3(sK2))
            & v12_waybel_0(X1,k7_lattice3(sK2))
            & v1_waybel_0(X1,k7_lattice3(sK2))
            & ~ v1_xboole_0(X1) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            & v2_waybel_7(X1,sK2)
            & v13_waybel_0(X1,sK2)
            & v2_waybel_0(X1,sK2)
            & ~ v1_xboole_0(X1) ) ) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
        | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
        | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
        | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v2_waybel_7(sK3,sK2)
        | ~ v13_waybel_0(sK3,sK2)
        | ~ v2_waybel_0(sK3,sK2)
        | v1_xboole_0(sK3) )
      & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
          & v1_waybel_7(sK3,k7_lattice3(sK2))
          & v12_waybel_0(sK3,k7_lattice3(sK2))
          & v1_waybel_0(sK3,k7_lattice3(sK2))
          & ~ v1_xboole_0(sK3) )
        | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
          & v2_waybel_7(sK3,sK2)
          & v13_waybel_0(sK3,sK2)
          & v2_waybel_0(sK3,sK2)
          & ~ v1_xboole_0(sK3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_7)).

fof(f199,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f46,f196])).

fof(f46,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f194,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f47,f191])).

fof(f47,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f189,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f48,f186])).

fof(f48,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f184,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f49,f181])).

fof(f49,plain,(
    v2_lattice3(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f179,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f50,f176])).

fof(f50,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f174,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f111,f130])).

fof(f111,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f168,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f57,f134,f114])).

fof(f57,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f167,plain,
    ( spl5_2
    | spl5_6 ),
    inference(avatar_split_clause,[],[f58,f134,f118])).

fof(f58,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,
    ( spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f59,f134,f122])).

fof(f59,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f165,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f60,f134,f126])).

fof(f60,plain,
    ( v1_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f62,f138,f114])).

fof(f62,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f162,plain,
    ( spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f63,f138,f118])).

fof(f63,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f161,plain,
    ( spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f64,f138,f122])).

fof(f64,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f160,plain,
    ( spl5_4
    | spl5_7 ),
    inference(avatar_split_clause,[],[f65,f138,f126])).

fof(f65,plain,
    ( v12_waybel_0(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f158,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f67,f142,f114])).

fof(f67,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f157,plain,
    ( spl5_2
    | spl5_8 ),
    inference(avatar_split_clause,[],[f68,f142,f118])).

fof(f68,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f156,plain,
    ( spl5_3
    | spl5_8 ),
    inference(avatar_split_clause,[],[f69,f142,f122])).

fof(f69,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,
    ( spl5_4
    | spl5_8 ),
    inference(avatar_split_clause,[],[f70,f142,f126])).

fof(f70,plain,
    ( v1_waybel_7(sK3,k7_lattice3(sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f153,plain,
    ( spl5_1
    | spl5_9 ),
    inference(avatar_split_clause,[],[f72,f146,f114])).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v2_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f152,plain,
    ( spl5_2
    | spl5_9 ),
    inference(avatar_split_clause,[],[f73,f146,f118])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f151,plain,
    ( spl5_3
    | spl5_9 ),
    inference(avatar_split_clause,[],[f74,f146,f122])).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | v2_waybel_7(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f150,plain,
    ( spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f75,f146,f126])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f149,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f112,f146,f142,f138,f134,f130,f126,f122,f118,f114])).

fof(f112,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK2))))
    | ~ v1_waybel_7(sK3,k7_lattice3(sK2))
    | ~ v12_waybel_0(sK3,k7_lattice3(sK2))
    | ~ v1_waybel_0(sK3,k7_lattice3(sK2))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_7(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2)
    | ~ v2_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
