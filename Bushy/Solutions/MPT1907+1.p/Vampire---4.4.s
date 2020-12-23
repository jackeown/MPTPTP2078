%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t75_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 982 expanded)
%              Number of leaves         :   62 ( 441 expanded)
%              Depth                    :   10
%              Number of atoms          : 1136 (4131 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f116,f123,f130,f137,f144,f151,f158,f165,f172,f182,f194,f201,f213,f221,f229,f241,f249,f259,f280,f288,f296,f304,f312,f320,f329,f336,f344,f352,f360,f368,f376,f384,f392,f400,f409,f425,f433,f441,f449,f457,f465,f473,f486,f509,f511,f513,f515,f517,f519,f521,f523,f525,f527,f529,f531])).

fof(f531,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f496,f485])).

fof(f485,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl8_86
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f496,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f328,f408,f391,f448,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_borsuk_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ( v3_borsuk_1(sK5(X0,X1),X0,X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(sK5(X0,X1),X0,X1)
                & v1_funct_2(sK5(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(sK5(X0,X1)) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( v3_borsuk_1(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X3,X0,X1)
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( v3_borsuk_1(sK5(X0,X1),X0,X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK5(X0,X1),X0,X1)
        & v1_funct_2(sK5(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ? [X3] :
                  ( v3_borsuk_1(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ? [X2] :
                  ( v3_borsuk_1(X2,X0,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',d20_borsuk_1)).

fof(f448,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl8_78
  <=> v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f391,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl8_66
  <=> v5_pre_topc(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f408,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl8_70
  <=> v3_borsuk_1(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f328,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl8_50
  <=> v1_funct_1(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f164,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_16
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f171,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_19
  <=> ~ r1_borsuk_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f136,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_9
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f129,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f115,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f108,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f529,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f497,f448])).

fof(f497,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f328,f408,f391,f485,f93])).

fof(f527,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f498,f391])).

fof(f498,plain,
    ( ~ v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f328,f408,f448,f485,f93])).

fof(f525,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f499,f408])).

fof(f499,plain,
    ( ~ v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f328,f391,f448,f485,f93])).

fof(f523,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f500,f328])).

fof(f500,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f408,f391,f448,f485,f93])).

fof(f521,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f501,f164])).

fof(f501,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f328,f408,f391,f448,f485,f93])).

fof(f519,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f502,f171])).

fof(f502,plain,
    ( r1_borsuk_1(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f164,f328,f408,f391,f448,f485,f93])).

fof(f517,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f503,f136])).

fof(f503,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f171,f164,f328,f408,f391,f448,f485,f93])).

fof(f515,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f504,f129])).

fof(f504,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f136,f171,f164,f328,f408,f391,f448,f485,f93])).

fof(f513,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f505,f115])).

fof(f505,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f129,f136,f171,f164,f328,f408,f391,f448,f485,f93])).

fof(f511,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f506,f108])).

fof(f506,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f115,f129,f136,f171,f164,f328,f408,f391,f448,f485,f93])).

fof(f509,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_70
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f108,f115,f129,f136,f171,f164,f328,f408,f391,f448,f485,f93])).

fof(f486,plain,
    ( spl8_86
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f479,f163,f156,f135,f128,f121,f114,f107,f484])).

fof(f121,plain,
    ( spl8_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f156,plain,
    ( spl8_14
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f479,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f108,f115,f122,f129,f136,f157,f164,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK4(X0,X1),X0,X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK4(X0,X1),X0,X1)
            & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK4(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( v3_borsuk_1(sK4(X0,X1),X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK4(X0,X1),X0,X1)
        & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',t74_tex_2)).

fof(f157,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f122,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f473,plain,
    ( spl8_84
    | ~ spl8_68
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f466,f463,f398,f471])).

fof(f471,plain,
    ( spl8_84
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f398,plain,
    ( spl8_68
  <=> l1_pre_topc(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f463,plain,
    ( spl8_82
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f466,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl8_68
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f399,f464,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',dt_m1_pre_topc)).

fof(f464,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f463])).

fof(f399,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f398])).

fof(f465,plain,
    ( spl8_82
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f401,f398,f463])).

fof(f401,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_68 ),
    inference(unit_resulting_resolution,[],[f399,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',existence_m1_pre_topc)).

fof(f457,plain,
    ( spl8_80
    | ~ spl8_62
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f450,f439,f374,f455])).

fof(f455,plain,
    ( spl8_80
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f374,plain,
    ( spl8_62
  <=> l1_pre_topc(sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f439,plain,
    ( spl8_76
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f450,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK7)))))
    | ~ spl8_62
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f375,f440,f80])).

fof(f440,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f439])).

fof(f375,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f374])).

fof(f449,plain,
    ( spl8_78
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f442,f163,f156,f135,f128,f121,f114,f107,f447])).

fof(f442,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f108,f115,f122,f129,f136,f157,f164,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f441,plain,
    ( spl8_76
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f377,f374,f439])).

fof(f377,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f375,f81])).

fof(f433,plain,
    ( spl8_74
    | ~ spl8_58
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f426,f423,f358,f431])).

fof(f431,plain,
    ( spl8_74
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f358,plain,
    ( spl8_58
  <=> l1_pre_topc(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f423,plain,
    ( spl8_72
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f426,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl8_58
    | ~ spl8_72 ),
    inference(unit_resulting_resolution,[],[f359,f424,f80])).

fof(f424,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f423])).

fof(f359,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f358])).

fof(f425,plain,
    ( spl8_72
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f361,f358,f423])).

fof(f361,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f359,f81])).

fof(f409,plain,
    ( spl8_70
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f402,f163,f156,f135,f128,f121,f114,f107,f407])).

fof(f402,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f108,f115,f122,f129,f136,f157,f164,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_borsuk_1(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f400,plain,
    ( spl8_68
    | ~ spl8_54
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f393,f382,f342,f398])).

fof(f342,plain,
    ( spl8_54
  <=> l1_pre_topc(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f382,plain,
    ( spl8_64
  <=> m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f393,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_54
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f343,f383,f80])).

fof(f383,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f382])).

fof(f343,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f342])).

fof(f392,plain,
    ( spl8_66
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f385,f163,f156,f135,f128,f121,f114,f107,f390])).

fof(f385,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f108,f115,f122,f129,f136,f157,f164,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f384,plain,
    ( spl8_64
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f345,f342,f382])).

fof(f345,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_54 ),
    inference(unit_resulting_resolution,[],[f343,f81])).

fof(f376,plain,
    ( spl8_62
    | ~ spl8_48
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f369,f366,f318,f374])).

fof(f318,plain,
    ( spl8_48
  <=> l1_pre_topc(sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f366,plain,
    ( spl8_60
  <=> m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f369,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_48
    | ~ spl8_60 ),
    inference(unit_resulting_resolution,[],[f319,f367,f80])).

fof(f367,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f366])).

fof(f319,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f318])).

fof(f368,plain,
    ( spl8_60
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f321,f318,f366])).

fof(f321,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_48 ),
    inference(unit_resulting_resolution,[],[f319,f81])).

fof(f360,plain,
    ( spl8_58
    | ~ spl8_44
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f353,f350,f302,f358])).

fof(f302,plain,
    ( spl8_44
  <=> l1_pre_topc(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f350,plain,
    ( spl8_56
  <=> m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f353,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_44
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f303,f351,f80])).

fof(f351,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f350])).

fof(f303,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f302])).

fof(f352,plain,
    ( spl8_56
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f305,f302,f350])).

fof(f305,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f303,f81])).

fof(f344,plain,
    ( spl8_54
    | ~ spl8_34
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f337,f334,f247,f342])).

fof(f247,plain,
    ( spl8_34
  <=> l1_pre_topc(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f334,plain,
    ( spl8_52
  <=> m1_pre_topc(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f337,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_34
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f248,f335,f80])).

fof(f335,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f334])).

fof(f248,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f247])).

fof(f336,plain,
    ( spl8_52
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f250,f247,f334])).

fof(f250,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f248,f81])).

fof(f329,plain,
    ( spl8_50
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f322,f163,f156,f135,f128,f121,f114,f107,f327])).

fof(f322,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f108,f115,f122,f129,f136,f157,f164,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f320,plain,
    ( spl8_48
    | ~ spl8_30
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f313,f310,f227,f318])).

fof(f227,plain,
    ( spl8_30
  <=> l1_pre_topc(sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f310,plain,
    ( spl8_46
  <=> m1_pre_topc(sK3(sK3(sK7)),sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f313,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_30
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f228,f311,f80])).

fof(f311,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f310])).

fof(f228,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f312,plain,
    ( spl8_46
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f234,f227,f310])).

fof(f234,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f228,f81])).

fof(f304,plain,
    ( spl8_44
    | ~ spl8_28
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f297,f294,f219,f302])).

fof(f219,plain,
    ( spl8_28
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f294,plain,
    ( spl8_42
  <=> m1_pre_topc(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f297,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_28
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f220,f295,f80])).

fof(f295,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f294])).

fof(f220,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f219])).

fof(f296,plain,
    ( spl8_42
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f222,f219,f294])).

fof(f222,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f220,f81])).

fof(f288,plain,
    ( spl8_40
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f281,f278,f286])).

fof(f286,plain,
    ( spl8_40
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f278,plain,
    ( spl8_38
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f281,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_38 ),
    inference(superposition,[],[f94,f279])).

fof(f279,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f278])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',existence_m1_subset_1)).

fof(f280,plain,
    ( spl8_38
    | ~ spl8_10
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f265,f257,f142,f278])).

fof(f142,plain,
    ( spl8_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f257,plain,
    ( spl8_36
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f265,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_10
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f258,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f173,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',t6_boole)).

fof(f173,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f143,f82])).

fof(f143,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f258,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl8_36
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f252,f142,f257])).

fof(f252,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f94,f251,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',t2_subset)).

fof(f251,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f143,f94,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',t5_subset)).

fof(f249,plain,
    ( spl8_34
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f242,f239,f211,f247])).

fof(f211,plain,
    ( spl8_26
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f239,plain,
    ( spl8_32
  <=> m1_pre_topc(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f242,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f212,f240,f80])).

fof(f240,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f239])).

fof(f212,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f241,plain,
    ( spl8_32
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f214,f211,f239])).

fof(f214,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f212,f81])).

fof(f229,plain,
    ( spl8_30
    | ~ spl8_12
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f204,f199,f149,f227])).

fof(f149,plain,
    ( spl8_12
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f199,plain,
    ( spl8_24
  <=> m1_pre_topc(sK3(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f204,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_12
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f150,f200,f80])).

fof(f200,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f199])).

fof(f150,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f221,plain,
    ( spl8_28
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f203,f192,f128,f219])).

fof(f192,plain,
    ( spl8_22
  <=> m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f203,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f129,f193,f80])).

fof(f193,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f213,plain,
    ( spl8_26
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f202,f163,f128,f211])).

fof(f202,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f129,f164,f80])).

fof(f201,plain,
    ( spl8_24
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f187,f149,f199])).

fof(f187,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f150,f81])).

fof(f194,plain,
    ( spl8_22
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f186,f128,f192])).

fof(f186,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f129,f81])).

fof(f182,plain,
    ( spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f173,f142,f180])).

fof(f180,plain,
    ( spl8_20
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f172,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f76,f170])).

fof(f76,plain,(
    ~ r1_borsuk_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    & m1_pre_topc(sK1,sK0)
    & v4_tex_2(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK0,X1)
          & m1_pre_topc(X1,sK0)
          & v4_tex_2(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_borsuk_1(X0,sK1)
        & m1_pre_topc(sK1,X0)
        & v4_tex_2(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',t75_tex_2)).

fof(f165,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f75,f163])).

fof(f75,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f158,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f74,f156])).

fof(f74,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f151,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f102,f149])).

fof(f102,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f67])).

fof(f67,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',existence_l1_pre_topc)).

fof(f144,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f77,f142])).

fof(f77,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t75_tex_2.p',dt_o_0_0_xboole_0)).

fof(f137,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f73,f135])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f130,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f72,f128])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f123,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f71,f121])).

fof(f71,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f70,f114])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f109,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f69,f107])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
