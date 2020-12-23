%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t68_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:47 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 877 expanded)
%              Number of leaves         :   57 ( 368 expanded)
%              Depth                    :    9
%              Number of atoms          :  928 (3829 expanded)
%              Number of equality atoms :   20 ( 204 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f109,f116,f123,f130,f137,f144,f151,f158,f165,f172,f179,f186,f193,f200,f207,f215,f225,f232,f239,f250,f257,f264,f275,f283,f291,f298,f314,f322,f336,f348,f360,f368,f378,f385,f395,f405,f413,f428,f430,f432,f434,f436,f438,f440,f442,f444,f446,f448])).

fof(f448,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f416,f263])).

fof(f263,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_45
  <=> k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f416,plain,
    ( k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f386,f199,f206,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t64_yellow_0)).

fof(f206,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_30
  <=> r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f199,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl7_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f386,plain,
    ( ! [X0] : r2_yellow_0(sK0,X0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f101,f115,f122,f129,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t17_yellow_0)).

fof(f122,plain,
    ( v3_lattice3(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_6
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f115,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f192,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_26
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f185,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_24
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f136,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_11
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f129,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f108,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f101,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f446,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f417,f206])).

fof(f417,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f386,f199,f263,f80])).

fof(f444,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f418,f199])).

fof(f418,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f386,f206,f263,f80])).

fof(f442,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f419,f386])).

fof(f419,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f199,f206,f263,f80])).

fof(f440,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f420,f192])).

fof(f420,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f386,f199,f206,f263,f80])).

fof(f438,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f421,f185])).

fof(f421,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f192,f386,f199,f206,f263,f80])).

fof(f436,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f422,f136])).

fof(f422,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f185,f192,f386,f199,f206,f263,f80])).

fof(f434,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f423,f129])).

fof(f423,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f136,f185,f192,f386,f199,f206,f263,f80])).

fof(f432,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f424,f108])).

fof(f424,plain,
    ( ~ v4_orders_2(sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f129,f136,f185,f192,f386,f199,f206,f263,f80])).

fof(f430,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f425,f101])).

fof(f425,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f108,f129,f136,f185,f192,f386,f199,f206,f263,f80])).

fof(f428,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f386,f199,f206,f263,f80])).

fof(f413,plain,
    ( spl7_74
    | ~ spl7_52
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f406,f383,f296,f411])).

fof(f411,plain,
    ( spl7_74
  <=> l1_orders_2(sK3(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f296,plain,
    ( spl7_52
  <=> l1_orders_2(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f383,plain,
    ( spl7_68
  <=> m1_yellow_0(sK3(sK3(sK6)),sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f406,plain,
    ( l1_orders_2(sK3(sK3(sK6)))
    | ~ spl7_52
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f297,f384,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',dt_m1_yellow_0)).

fof(f384,plain,
    ( m1_yellow_0(sK3(sK3(sK6)),sK3(sK6))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f383])).

fof(f297,plain,
    ( l1_orders_2(sK3(sK6))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f296])).

fof(f405,plain,
    ( spl7_72
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f398,f205,f198,f191,f184,f135,f128,f121,f114,f107,f100,f403])).

fof(f403,plain,
    ( spl7_72
  <=> r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f398,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f101,f108,f129,f136,f185,f192,f386,f199,f206,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,X2)
      | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f395,plain,
    ( spl7_70
    | ~ spl7_50
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f388,f376,f289,f393])).

fof(f393,plain,
    ( spl7_70
  <=> l1_orders_2(sK3(sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f289,plain,
    ( spl7_50
  <=> l1_orders_2(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f376,plain,
    ( spl7_66
  <=> m1_yellow_0(sK3(sK3(sK5)),sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f388,plain,
    ( l1_orders_2(sK3(sK3(sK5)))
    | ~ spl7_50
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f290,f377,f76])).

fof(f377,plain,
    ( m1_yellow_0(sK3(sK3(sK5)),sK3(sK5))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f376])).

fof(f290,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f289])).

fof(f385,plain,
    ( spl7_68
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f307,f296,f383])).

fof(f307,plain,
    ( m1_yellow_0(sK3(sK3(sK6)),sK3(sK6))
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f297,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
     => m1_yellow_0(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_yellow_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',existence_m1_yellow_0)).

fof(f378,plain,
    ( spl7_66
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f299,f289,f376])).

fof(f299,plain,
    ( m1_yellow_0(sK3(sK3(sK5)),sK3(sK5))
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f290,f77])).

fof(f368,plain,
    ( spl7_64
    | ~ spl7_48
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f361,f346,f281,f366])).

fof(f366,plain,
    ( spl7_64
  <=> l1_orders_2(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f281,plain,
    ( spl7_48
  <=> l1_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f346,plain,
    ( spl7_60
  <=> m1_yellow_0(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f361,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl7_48
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f282,f347,f76])).

fof(f347,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f346])).

fof(f282,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f281])).

fof(f360,plain,
    ( ~ spl7_63
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f339,f334,f358])).

fof(f358,plain,
    ( spl7_63
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f334,plain,
    ( spl7_58
  <=> r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f339,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(u1_struct_0(sK1)))
    | ~ spl7_58 ),
    inference(unit_resulting_resolution,[],[f335,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',antisymmetry_r2_hidden)).

fof(f335,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f334])).

fof(f348,plain,
    ( spl7_60
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f284,f281,f346])).

fof(f284,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f282,f77])).

fof(f336,plain,
    ( spl7_58
    | spl7_33 ),
    inference(avatar_split_clause,[],[f325,f213,f334])).

fof(f213,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f325,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f81,f214,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t2_subset)).

fof(f214,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f213])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',existence_m1_subset_1)).

fof(f322,plain,
    ( spl7_56
    | ~ spl7_46
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f315,f312,f273,f320])).

fof(f320,plain,
    ( spl7_56
  <=> l1_orders_2(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f273,plain,
    ( spl7_46
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f312,plain,
    ( spl7_54
  <=> m1_yellow_0(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f315,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl7_46
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f274,f313,f76])).

fof(f313,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f312])).

fof(f274,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f273])).

fof(f314,plain,
    ( spl7_54
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f276,f273,f312])).

fof(f276,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f274,f77])).

fof(f298,plain,
    ( spl7_52
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f268,f237,f149,f296])).

fof(f149,plain,
    ( spl7_14
  <=> l1_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f237,plain,
    ( spl7_38
  <=> m1_yellow_0(sK3(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f268,plain,
    ( l1_orders_2(sK3(sK6))
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f150,f238,f76])).

fof(f238,plain,
    ( m1_yellow_0(sK3(sK6),sK6)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f237])).

fof(f150,plain,
    ( l1_orders_2(sK6)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f291,plain,
    ( spl7_50
    | ~ spl7_12
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f267,f230,f142,f289])).

fof(f142,plain,
    ( spl7_12
  <=> l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f230,plain,
    ( spl7_36
  <=> m1_yellow_0(sK3(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f267,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ spl7_12
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f143,f231,f76])).

fof(f231,plain,
    ( m1_yellow_0(sK3(sK5),sK5)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f230])).

fof(f143,plain,
    ( l1_orders_2(sK5)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f283,plain,
    ( spl7_48
    | ~ spl7_8
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f266,f223,f128,f281])).

fof(f223,plain,
    ( spl7_34
  <=> m1_yellow_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f266,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl7_8
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f129,f224,f76])).

fof(f224,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f275,plain,
    ( spl7_46
    | ~ spl7_8
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f265,f191,f128,f273])).

fof(f265,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_8
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f129,f192,f76])).

fof(f264,plain,(
    ~ spl7_45 ),
    inference(avatar_split_clause,[],[f74,f262])).

fof(f74,plain,(
    k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    & r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f54,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( k2_yellow_0(sK1,X2) != k2_yellow_0(X0,X2)
            & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(sK1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
          & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_yellow_0(X0,sK2) != k2_yellow_0(X1,sK2)
        & r2_hidden(k2_yellow_0(X0,sK2),u1_struct_0(X1))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t68_yellow_0)).

fof(f257,plain,
    ( spl7_42
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f243,f205,f255])).

fof(f255,plain,
    ( spl7_42
  <=> m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f243,plain,
    ( m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f206,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t1_subset)).

fof(f250,plain,
    ( ~ spl7_41
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f241,f205,f248])).

fof(f248,plain,
    ( spl7_41
  <=> ~ r2_hidden(u1_struct_0(sK1),k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f241,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k2_yellow_0(sK0,sK2))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f206,f83])).

fof(f239,plain,
    ( spl7_38
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f218,f149,f237])).

fof(f218,plain,
    ( m1_yellow_0(sK3(sK6),sK6)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f150,f77])).

fof(f232,plain,
    ( spl7_36
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f217,f142,f230])).

fof(f217,plain,
    ( m1_yellow_0(sK3(sK5),sK5)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f143,f77])).

fof(f225,plain,
    ( spl7_34
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f216,f128,f223])).

fof(f216,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f129,f77])).

fof(f215,plain,
    ( ~ spl7_33
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f208,f205,f213])).

fof(f208,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f206,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',t7_boole)).

fof(f207,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f73,f205])).

fof(f73,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f200,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f72,f198])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f193,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f71,f191])).

fof(f71,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f186,plain,(
    spl7_24 ),
    inference(avatar_split_clause,[],[f70,f184])).

fof(f70,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f179,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f95,f177])).

fof(f177,plain,
    ( spl7_22
  <=> v3_lattice3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f95,plain,(
    v3_lattice3(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( v3_lattice3(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & ~ v2_struct_0(sK6)
    & l1_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0)
        & l1_orders_2(X0) )
   => ( v3_lattice3(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & ~ v2_struct_0(sK6)
      & l1_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,axiom,(
    ? [X0] :
      ( v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v2_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',rc2_yellow_0)).

fof(f172,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f94,f170])).

fof(f170,plain,
    ( spl7_20
  <=> v5_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f94,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f165,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f93,f163])).

fof(f163,plain,
    ( spl7_18
  <=> v4_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f93,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f158,plain,(
    ~ spl7_17 ),
    inference(avatar_split_clause,[],[f92,f156])).

fof(f156,plain,
    ( spl7_17
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f92,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f151,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f91,f149])).

fof(f91,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f144,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f90,f142])).

fof(f90,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f60])).

fof(f60,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK5) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t68_yellow_0.p',existence_l1_orders_2)).

fof(f137,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f69,f135])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f130,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f68,f128])).

fof(f68,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f123,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f67,f121])).

fof(f67,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f66,f114])).

fof(f66,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f109,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f65,f107])).

fof(f65,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f64,f100])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
