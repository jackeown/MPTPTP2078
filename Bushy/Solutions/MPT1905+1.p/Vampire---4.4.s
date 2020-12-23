%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t73_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  268 (1005 expanded)
%              Number of leaves         :   64 ( 451 expanded)
%              Depth                    :   10
%              Number of atoms          : 1169 (4101 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f126,f133,f140,f147,f154,f161,f168,f175,f185,f197,f204,f214,f224,f232,f240,f252,f260,f269,f278,f299,f307,f315,f324,f331,f340,f347,f355,f363,f371,f380,f388,f395,f403,f411,f419,f427,f444,f452,f461,f468,f476,f484,f492,f501,f533,f535,f537,f539,f541,f543,f545,f547,f549,f551,f553,f555])).

fof(f555,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f520,f500])).

fof(f500,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl8_88
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f520,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f339,f402,f387,f460,f103])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).

fof(f72,plain,(
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

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

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
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',d20_borsuk_1)).

fof(f460,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl8_78
  <=> v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f387,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl8_62
  <=> v5_pre_topc(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f402,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl8_66
  <=> v3_borsuk_1(sK4(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f339,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl8_50
  <=> v1_funct_1(sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f167,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_14
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f174,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_17
  <=> ~ r1_borsuk_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f146,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_9
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f139,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f125,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f118,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f553,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f521,f460])).

fof(f521,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f339,f402,f387,f500,f103])).

fof(f551,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f522,f387])).

fof(f522,plain,
    ( ~ v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f339,f402,f460,f500,f103])).

fof(f549,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f523,f402])).

fof(f523,plain,
    ( ~ v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f339,f387,f460,f500,f103])).

fof(f547,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f524,f339])).

fof(f524,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f402,f387,f460,f500,f103])).

fof(f545,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f525,f167])).

fof(f525,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f339,f402,f387,f460,f500,f103])).

fof(f543,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f526,f174])).

fof(f526,plain,
    ( r1_borsuk_1(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f167,f339,f402,f387,f460,f500,f103])).

fof(f541,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f527,f146])).

fof(f527,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f174,f167,f339,f402,f387,f460,f500,f103])).

fof(f539,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f528,f139])).

fof(f528,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f146,f174,f167,f339,f402,f387,f460,f500,f103])).

fof(f537,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f529,f125])).

fof(f529,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f139,f146,f174,f167,f339,f402,f387,f460,f500,f103])).

fof(f535,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f530,f118])).

fof(f530,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f125,f139,f146,f174,f167,f339,f402,f387,f460,f500,f103])).

fof(f533,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14
    | spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_50
    | ~ spl8_62
    | ~ spl8_66
    | ~ spl8_78
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f118,f125,f139,f146,f174,f167,f339,f402,f387,f460,f500,f103])).

fof(f501,plain,
    ( spl8_88
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f493,f166,f145,f138,f131,f124,f117,f499])).

fof(f131,plain,
    ( spl8_4
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f493,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f146,f167,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK4(X0,X1),X0,X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK4(X0,X1),X0,X1)
            & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK4(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f68])).

fof(f68,plain,(
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

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',t72_tex_2)).

fof(f132,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f492,plain,
    ( spl8_86
    | ~ spl8_72
    | ~ spl8_84 ),
    inference(avatar_split_clause,[],[f485,f482,f425,f490])).

fof(f490,plain,
    ( spl8_86
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f425,plain,
    ( spl8_72
  <=> l1_pre_topc(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f482,plain,
    ( spl8_84
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f485,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl8_72
    | ~ spl8_84 ),
    inference(unit_resulting_resolution,[],[f426,f483,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',dt_m1_pre_topc)).

fof(f483,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f482])).

fof(f426,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f425])).

fof(f484,plain,
    ( spl8_84
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f428,f425,f482])).

fof(f428,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl8_72 ),
    inference(unit_resulting_resolution,[],[f426,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',existence_m1_pre_topc)).

fof(f476,plain,
    ( spl8_82
    | ~ spl8_68
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f469,f466,f409,f474])).

fof(f474,plain,
    ( spl8_82
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f409,plain,
    ( spl8_68
  <=> l1_pre_topc(sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f466,plain,
    ( spl8_80
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f469,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK7)))))
    | ~ spl8_68
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f410,f467,f89])).

fof(f467,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f466])).

fof(f410,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f409])).

fof(f468,plain,
    ( spl8_80
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f412,f409,f466])).

fof(f412,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK7)))),sK3(sK3(sK3(sK7))))
    | ~ spl8_68 ),
    inference(unit_resulting_resolution,[],[f410,f90])).

fof(f461,plain,
    ( spl8_78
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f453,f166,f145,f138,f131,f124,f117,f459])).

fof(f453,plain,
    ( v1_funct_2(sK4(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f146,f167,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f452,plain,
    ( spl8_76
    | ~ spl8_60
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f445,f442,f378,f450])).

fof(f450,plain,
    ( spl8_76
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f378,plain,
    ( spl8_60
  <=> l1_pre_topc(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f442,plain,
    ( spl8_74
  <=> m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f445,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl8_60
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f379,f443,f89])).

fof(f443,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f442])).

fof(f379,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f378])).

fof(f444,plain,
    ( spl8_74
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f381,f378,f442])).

fof(f381,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl8_60 ),
    inference(unit_resulting_resolution,[],[f379,f90])).

fof(f427,plain,
    ( spl8_72
    | ~ spl8_56
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f420,f417,f361,f425])).

fof(f361,plain,
    ( spl8_56
  <=> l1_pre_topc(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f417,plain,
    ( spl8_70
  <=> m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f420,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl8_56
    | ~ spl8_70 ),
    inference(unit_resulting_resolution,[],[f362,f418,f89])).

fof(f418,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f417])).

fof(f362,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f361])).

fof(f419,plain,
    ( spl8_70
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f364,f361,f417])).

fof(f364,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f362,f90])).

fof(f411,plain,
    ( spl8_68
    | ~ spl8_52
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f404,f393,f345,f409])).

fof(f345,plain,
    ( spl8_52
  <=> l1_pre_topc(sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f393,plain,
    ( spl8_64
  <=> m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f404,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK7))))
    | ~ spl8_52
    | ~ spl8_64 ),
    inference(unit_resulting_resolution,[],[f346,f394,f89])).

fof(f394,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f393])).

fof(f346,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f403,plain,
    ( spl8_66
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f396,f166,f145,f138,f131,f124,f117,f401])).

fof(f396,plain,
    ( v3_borsuk_1(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f146,f167,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v3_borsuk_1(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f395,plain,
    ( spl8_64
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f348,f345,f393])).

fof(f348,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK7))),sK3(sK3(sK7)))
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f346,f90])).

fof(f388,plain,
    ( spl8_62
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f373,f166,f145,f138,f131,f124,f117,f386])).

fof(f373,plain,
    ( v5_pre_topc(sK4(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f146,f167,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK4(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f380,plain,
    ( spl8_60
    | ~ spl8_36
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f372,f369,f267,f378])).

fof(f267,plain,
    ( spl8_36
  <=> l1_pre_topc(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f369,plain,
    ( spl8_58
  <=> m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f372,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl8_36
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f268,f370,f89])).

fof(f370,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f369])).

fof(f268,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f267])).

fof(f371,plain,
    ( spl8_58
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f270,f267,f369])).

fof(f270,plain,
    ( m1_pre_topc(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f268,f90])).

fof(f363,plain,
    ( spl8_56
    | ~ spl8_32
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f356,f353,f250,f361])).

fof(f250,plain,
    ( spl8_32
  <=> l1_pre_topc(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f353,plain,
    ( spl8_54
  <=> m1_pre_topc(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f356,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl8_32
    | ~ spl8_54 ),
    inference(unit_resulting_resolution,[],[f251,f354,f89])).

fof(f354,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f353])).

fof(f251,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f250])).

fof(f355,plain,
    ( spl8_54
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f253,f250,f353])).

fof(f253,plain,
    ( m1_pre_topc(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f251,f90])).

fof(f347,plain,
    ( spl8_52
    | ~ spl8_28
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f332,f313,f230,f345])).

fof(f230,plain,
    ( spl8_28
  <=> l1_pre_topc(sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f313,plain,
    ( spl8_44
  <=> m1_pre_topc(sK3(sK3(sK7)),sK3(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f332,plain,
    ( l1_pre_topc(sK3(sK3(sK7)))
    | ~ spl8_28
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f231,f314,f89])).

fof(f314,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f313])).

fof(f231,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f340,plain,
    ( spl8_50
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_9
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f333,f166,f145,f138,f131,f124,f117,f338])).

fof(f333,plain,
    ( v1_funct_1(sK4(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f146,f167,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f331,plain,
    ( spl8_48
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f317,f195,f138,f131,f124,f117,f329])).

fof(f329,plain,
    ( spl8_48
  <=> v1_tdlat_3(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f195,plain,
    ( spl8_20
  <=> m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f317,plain,
    ( v1_tdlat_3(sK3(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f196,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',cc5_tdlat_3)).

fof(f196,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f324,plain,
    ( spl8_46
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f316,f166,f138,f131,f124,f117,f322])).

fof(f322,plain,
    ( spl8_46
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f316,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f118,f125,f132,f139,f167,f92])).

fof(f315,plain,
    ( spl8_44
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f233,f230,f313])).

fof(f233,plain,
    ( m1_pre_topc(sK3(sK3(sK7)),sK3(sK7))
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f231,f90])).

fof(f307,plain,
    ( spl8_42
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f300,f297,f305])).

fof(f305,plain,
    ( spl8_42
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f297,plain,
    ( spl8_40
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f300,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_40 ),
    inference(superposition,[],[f104,f298])).

fof(f298,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f297])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',existence_m1_subset_1)).

fof(f299,plain,
    ( spl8_40
    | ~ spl8_10
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f284,f276,f152,f297])).

fof(f152,plain,
    ( spl8_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f276,plain,
    ( spl8_38
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f284,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_10
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f277,f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f176,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',t6_boole)).

fof(f176,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f153,f91])).

fof(f153,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f277,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( spl8_38
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f271,f152,f276])).

fof(f271,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f104,f262,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',t2_subset)).

fof(f262,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f153,f104,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',t5_subset)).

fof(f269,plain,
    ( spl8_36
    | ~ spl8_26
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f261,f258,f222,f267])).

fof(f222,plain,
    ( spl8_26
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f258,plain,
    ( spl8_34
  <=> m1_pre_topc(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f261,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl8_26
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f223,f259,f89])).

fof(f259,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f258])).

fof(f223,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f260,plain,
    ( spl8_34
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f225,f222,f258])).

fof(f225,plain,
    ( m1_pre_topc(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f223,f90])).

fof(f252,plain,
    ( spl8_32
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f245,f238,f212,f250])).

fof(f212,plain,
    ( spl8_24
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f238,plain,
    ( spl8_30
  <=> m1_pre_topc(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f245,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f213,f239,f89])).

fof(f239,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f213,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f212])).

fof(f240,plain,
    ( spl8_30
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f215,f212,f238])).

fof(f215,plain,
    ( m1_pre_topc(sK3(sK1),sK1)
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f213,f90])).

fof(f232,plain,
    ( spl8_28
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f207,f202,f159,f230])).

fof(f159,plain,
    ( spl8_12
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f202,plain,
    ( spl8_22
  <=> m1_pre_topc(sK3(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f207,plain,
    ( l1_pre_topc(sK3(sK7))
    | ~ spl8_12
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f160,f203,f89])).

fof(f203,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f160,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f224,plain,
    ( spl8_26
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f206,f195,f138,f222])).

fof(f206,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl8_6
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f139,f196,f89])).

fof(f214,plain,
    ( spl8_24
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f205,f166,f138,f212])).

fof(f205,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f139,f167,f89])).

fof(f204,plain,
    ( spl8_22
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f190,f159,f202])).

fof(f190,plain,
    ( m1_pre_topc(sK3(sK7),sK7)
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f160,f90])).

fof(f197,plain,
    ( spl8_20
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f189,f138,f195])).

fof(f189,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f139,f90])).

fof(f185,plain,
    ( spl8_18
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f176,f152,f183])).

fof(f183,plain,
    ( spl8_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f175,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f84,f173])).

fof(f84,plain,(
    ~ r1_borsuk_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ~ r1_borsuk_1(sK0,sK1)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK0,X1)
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_borsuk_1(X0,sK1)
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',t73_tex_2)).

fof(f168,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f83,f166])).

fof(f83,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f161,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f112,f159])).

fof(f112,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f76])).

fof(f76,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',existence_l1_pre_topc)).

fof(f154,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f85,f152])).

fof(f85,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t73_tex_2.p',dt_o_0_0_xboole_0)).

fof(f147,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f82,f145])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f140,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f81,f138])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f133,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f80,f131])).

fof(f80,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f126,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f79,f124])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f119,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f78,f117])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
