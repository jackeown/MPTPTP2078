%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t79_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:57 EDT 2019

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
fof(f575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f127,f134,f141,f148,f155,f162,f169,f176,f183,f193,f205,f212,f224,f232,f240,f248,f256,f268,f276,f284,f293,f314,f322,f331,f339,f347,f355,f363,f371,f380,f387,f395,f403,f420,f428,f437,f444,f452,f460,f468,f476,f498,f527,f550,f552,f554,f556,f558,f560,f562,f564,f566,f568,f570,f572])).

fof(f572,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f537,f526])).

fof(f526,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl8_86
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f537,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f379,f459,f436,f497,f104])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f70,f71])).

fof(f71,plain,(
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

fof(f70,plain,(
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
    inference(rectify,[],[f69])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',d20_borsuk_1)).

fof(f497,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f496])).

fof(f496,plain,
    ( spl8_84
  <=> v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f436,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl8_72
  <=> v5_pre_topc(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f459,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl8_78
  <=> v3_borsuk_1(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f379,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl8_60
  <=> v1_funct_1(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f175,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl8_16
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f182,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_19
  <=> ~ r1_borsuk_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f147,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_9
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f140,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f126,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f119,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f570,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f538,f497])).

fof(f538,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f379,f459,f436,f526,f104])).

fof(f568,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f539,f436])).

fof(f539,plain,
    ( ~ v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f379,f459,f497,f526,f104])).

fof(f566,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f540,f459])).

fof(f540,plain,
    ( ~ v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f379,f436,f497,f526,f104])).

fof(f564,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f541,f379])).

fof(f541,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f459,f436,f497,f526,f104])).

fof(f562,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f542,f175])).

fof(f542,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f379,f459,f436,f497,f526,f104])).

fof(f560,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f543,f182])).

fof(f543,plain,
    ( r1_borsuk_1(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f175,f379,f459,f436,f497,f526,f104])).

fof(f558,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f544,f147])).

fof(f544,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f182,f175,f379,f459,f436,f497,f526,f104])).

fof(f556,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f545,f140])).

fof(f545,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f147,f182,f175,f379,f459,f436,f497,f526,f104])).

fof(f554,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f546,f126])).

fof(f546,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f140,f147,f182,f175,f379,f459,f436,f497,f526,f104])).

fof(f552,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f547,f119])).

fof(f547,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f126,f140,f147,f182,f175,f379,f459,f436,f497,f526,f104])).

fof(f550,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_16
    | spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_16
    | ~ spl8_19
    | ~ spl8_60
    | ~ spl8_72
    | ~ spl8_78
    | ~ spl8_84
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f119,f126,f140,f147,f182,f175,f379,f459,f436,f497,f526,f104])).

fof(f527,plain,
    ( spl8_86
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f520,f174,f153,f146,f139,f132,f125,f118,f525])).

fof(f132,plain,
    ( spl8_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f153,plain,
    ( spl8_10
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f520,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f119,f126,f133,f140,f147,f154,f175,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK4(X0,X1),X0,X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK4(X0,X1),X0,X1)
            & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK4(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f67])).

fof(f67,plain,(
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

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t78_tex_2)).

fof(f154,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f133,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f498,plain,
    ( spl8_84
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f489,f174,f153,f146,f139,f132,f125,f118,f496])).

fof(f489,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f119,f126,f133,f140,f147,f154,f175,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f476,plain,
    ( spl8_82
    | ~ spl8_66
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f469,f466,f401,f474])).

fof(f474,plain,
    ( spl8_82
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f401,plain,
    ( spl8_66
  <=> l1_pre_topc(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f466,plain,
    ( spl8_80
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f469,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl8_66
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f402,f467,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',dt_m1_pre_topc)).

fof(f467,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f466])).

fof(f402,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f401])).

fof(f468,plain,
    ( spl8_80
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f404,f401,f466])).

fof(f404,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_66 ),
    inference(unit_resulting_resolution,[],[f402,f91])).

fof(f91,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',existence_m1_pre_topc)).

fof(f460,plain,
    ( spl8_78
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f453,f174,f153,f146,f139,f132,f125,f118,f458])).

fof(f453,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f119,f126,f133,f140,f147,f154,f175,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v3_borsuk_1(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f452,plain,
    ( spl8_76
    | ~ spl8_62
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f445,f442,f385,f450])).

fof(f450,plain,
    ( spl8_76
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f385,plain,
    ( spl8_62
  <=> l1_pre_topc(sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f442,plain,
    ( spl8_74
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f445,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK7)))))
    | ~ spl8_62
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f386,f443,f90])).

fof(f443,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f442])).

fof(f386,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f385])).

fof(f444,plain,
    ( spl8_74
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f388,f385,f442])).

fof(f388,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f386,f91])).

fof(f437,plain,
    ( spl8_72
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f430,f174,f153,f146,f139,f132,f125,f118,f435])).

fof(f430,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f119,f126,f133,f140,f147,f154,f175,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f428,plain,
    ( spl8_70
    | ~ spl8_56
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f421,f418,f361,f426])).

fof(f426,plain,
    ( spl8_70
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f361,plain,
    ( spl8_56
  <=> l1_pre_topc(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f418,plain,
    ( spl8_68
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f421,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl8_56
    | ~ spl8_68 ),
    inference(unit_resulting_resolution,[],[f362,f419,f90])).

fof(f419,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f418])).

fof(f362,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f361])).

fof(f420,plain,
    ( spl8_68
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f364,f361,f418])).

fof(f364,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f362,f91])).

fof(f403,plain,
    ( spl8_66
    | ~ spl8_52
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f396,f393,f345,f401])).

fof(f345,plain,
    ( spl8_52
  <=> l1_pre_topc(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f393,plain,
    ( spl8_64
  <=> m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f396,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_52
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f346,f394,f90])).

fof(f394,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f393])).

fof(f346,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f395,plain,
    ( spl8_64
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f348,f345,f393])).

fof(f348,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f346,f91])).

fof(f387,plain,
    ( spl8_62
    | ~ spl8_48
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f372,f369,f329,f385])).

fof(f329,plain,
    ( spl8_48
  <=> l1_pre_topc(sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f369,plain,
    ( spl8_58
  <=> m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f372,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_48
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f330,f370,f90])).

fof(f370,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f369])).

fof(f330,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f329])).

fof(f380,plain,
    ( spl8_60
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f373,f174,f153,f146,f139,f132,f125,f118,f378])).

fof(f373,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f119,f126,f133,f140,f147,f154,f175,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f371,plain,
    ( spl8_58
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f332,f329,f369])).

fof(f332,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_48 ),
    inference(unit_resulting_resolution,[],[f330,f91])).

fof(f363,plain,
    ( spl8_56
    | ~ spl8_38
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f356,f353,f274,f361])).

fof(f274,plain,
    ( spl8_38
  <=> l1_pre_topc(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f353,plain,
    ( spl8_54
  <=> m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f356,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_38
    | ~ spl8_54 ),
    inference(unit_resulting_resolution,[],[f275,f354,f90])).

fof(f354,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f353])).

fof(f275,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f274])).

fof(f355,plain,
    ( spl8_54
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f277,f274,f353])).

fof(f277,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f275,f91])).

fof(f347,plain,
    ( spl8_52
    | ~ spl8_34
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f340,f337,f254,f345])).

fof(f254,plain,
    ( spl8_34
  <=> l1_pre_topc(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f337,plain,
    ( spl8_50
  <=> m1_pre_topc(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f340,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_34
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f255,f338,f90])).

fof(f338,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f337])).

fof(f255,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f254])).

fof(f339,plain,
    ( spl8_50
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f257,f254,f337])).

fof(f257,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f255,f91])).

fof(f331,plain,
    ( spl8_48
    | ~ spl8_30
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f324,f282,f238,f329])).

fof(f238,plain,
    ( spl8_30
  <=> l1_pre_topc(sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f282,plain,
    ( spl8_40
  <=> m1_pre_topc(sK3(sK3(sK7)),sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f324,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_30
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f239,f283,f90])).

fof(f283,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f282])).

fof(f239,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f322,plain,
    ( spl8_46
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f315,f312,f320])).

fof(f320,plain,
    ( spl8_46
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f312,plain,
    ( spl8_44
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f315,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_44 ),
    inference(superposition,[],[f105,f313])).

fof(f313,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f312])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',existence_m1_subset_1)).

fof(f314,plain,
    ( spl8_44
    | ~ spl8_12
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f299,f291,f160,f312])).

fof(f160,plain,
    ( spl8_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f291,plain,
    ( spl8_42
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f299,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_12
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f292,f186])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f184,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t6_boole)).

fof(f184,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f161,f92])).

fof(f161,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f292,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f291])).

fof(f293,plain,
    ( spl8_42
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f286,f160,f291])).

fof(f286,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f105,f285,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t2_subset)).

fof(f285,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f161,f105,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t5_subset)).

fof(f284,plain,
    ( spl8_40
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f241,f238,f282])).

fof(f241,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f239,f91])).

fof(f276,plain,
    ( spl8_38
    | ~ spl8_28
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f269,f266,f230,f274])).

fof(f230,plain,
    ( spl8_28
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f266,plain,
    ( spl8_36
  <=> m1_pre_topc(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f269,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_28
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f231,f267,f90])).

fof(f267,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f266])).

fof(f231,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f268,plain,
    ( spl8_36
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f233,f230,f266])).

fof(f233,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f231,f91])).

fof(f256,plain,
    ( spl8_34
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f249,f246,f222,f254])).

fof(f222,plain,
    ( spl8_26
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f246,plain,
    ( spl8_32
  <=> m1_pre_topc(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f249,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f223,f247,f90])).

fof(f247,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f246])).

fof(f223,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f248,plain,
    ( spl8_32
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f225,f222,f246])).

fof(f225,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f223,f91])).

fof(f240,plain,
    ( spl8_30
    | ~ spl8_14
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f215,f210,f167,f238])).

fof(f167,plain,
    ( spl8_14
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f210,plain,
    ( spl8_24
  <=> m1_pre_topc(sK3(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f215,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_14
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f168,f211,f90])).

fof(f211,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f168,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f232,plain,
    ( spl8_28
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f214,f203,f139,f230])).

fof(f203,plain,
    ( spl8_22
  <=> m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f214,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f140,f204,f90])).

fof(f204,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f224,plain,
    ( spl8_26
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f213,f174,f139,f222])).

fof(f213,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f140,f175,f90])).

fof(f212,plain,
    ( spl8_24
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f198,f167,f210])).

fof(f198,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f168,f91])).

fof(f205,plain,
    ( spl8_22
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f197,f139,f203])).

fof(f197,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f140,f91])).

fof(f193,plain,
    ( spl8_20
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f184,f160,f191])).

fof(f191,plain,
    ( spl8_20
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f183,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f84,f181])).

fof(f84,plain,(
    ~ r1_borsuk_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    & m1_pre_topc(sK1,sK0)
    & v1_tdlat_3(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK0,X1)
          & m1_pre_topc(X1,sK0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_borsuk_1(X0,sK1)
        & m1_pre_topc(sK1,X0)
        & v1_tdlat_3(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
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
              & v1_tdlat_3(X1)
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
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t79_tex_2)).

fof(f176,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f83,f174])).

fof(f83,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f169,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f113,f167])).

fof(f113,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f75])).

fof(f75,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',existence_l1_pre_topc)).

fof(f162,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f85,f160])).

fof(f85,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',dt_o_0_0_xboole_0)).

fof(f155,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f82,f153])).

fof(f82,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f148,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f81,f146])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f141,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f80,f139])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f134,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f79,f132])).

fof(f79,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f127,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f78,f125])).

fof(f78,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f120,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f77,f118])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
