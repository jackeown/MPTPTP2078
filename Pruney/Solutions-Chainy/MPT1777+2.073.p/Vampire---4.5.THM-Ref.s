%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:14 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  305 ( 765 expanded)
%              Number of leaves         :   74 ( 397 expanded)
%              Depth                    :   31
%              Number of atoms          : 1611 (6597 expanded)
%              Number of equality atoms :   80 ( 756 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1578,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f206,f212,f224,f250,f276,f281,f290,f295,f300,f322,f330,f369,f370,f373,f376,f384,f392,f402,f450,f453,f460,f618,f1113,f1370,f1438,f1455,f1525,f1555,f1576,f1577])).

fof(f1577,plain,
    ( ~ spl9_180
    | spl9_182 ),
    inference(avatar_split_clause,[],[f1556,f1552,f1518])).

fof(f1518,plain,
    ( spl9_180
  <=> sP0(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f1552,plain,
    ( spl9_182
  <=> v1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f1556,plain,
    ( ~ sP0(sK5,sK4)
    | spl9_182 ),
    inference(unit_resulting_resolution,[],[f1554,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1554,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | spl9_182 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f1576,plain,
    ( ~ spl9_39
    | ~ spl9_42
    | ~ spl9_49
    | ~ spl9_66
    | ~ spl9_170
    | spl9_181 ),
    inference(avatar_contradiction_clause,[],[f1575])).

fof(f1575,plain,
    ( $false
    | ~ spl9_39
    | ~ spl9_42
    | ~ spl9_49
    | ~ spl9_66
    | ~ spl9_170
    | spl9_181 ),
    inference(subsumption_resolution,[],[f1574,f1454])).

fof(f1454,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ spl9_170 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1452,plain,
    ( spl9_170
  <=> m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).

fof(f1574,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ spl9_39
    | ~ spl9_42
    | ~ spl9_49
    | ~ spl9_66
    | spl9_181 ),
    inference(forward_demodulation,[],[f1566,f391])).

fof(f391,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl9_42
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f1566,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl9_39
    | ~ spl9_49
    | ~ spl9_66
    | spl9_181 ),
    inference(unit_resulting_resolution,[],[f319,f617,f459,f1524,f199])).

fof(f199,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f100,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f100,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f1524,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK5)
    | spl9_181 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl9_181
  <=> v3_pre_topc(k2_struct_0(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_181])])).

fof(f459,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl9_49
  <=> v3_pre_topc(k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f617,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl9_66
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f319,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl9_39
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f1555,plain,
    ( ~ spl9_182
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f1550,f1367,f389,f381,f311,f306,f297,f278,f247,f209,f195,f190,f185,f180,f175,f170,f165,f160,f155,f150,f145,f105,f1552])).

fof(f105,plain,
    ( spl9_1
  <=> r1_tmap_1(sK5,sK3,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f145,plain,
    ( spl9_9
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f150,plain,
    ( spl9_10
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f155,plain,
    ( spl9_11
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f160,plain,
    ( spl9_12
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f165,plain,
    ( spl9_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f170,plain,
    ( spl9_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f175,plain,
    ( spl9_15
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f180,plain,
    ( spl9_16
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f185,plain,
    ( spl9_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f190,plain,
    ( spl9_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f195,plain,
    ( spl9_19
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f209,plain,
    ( spl9_21
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f247,plain,
    ( spl9_26
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f278,plain,
    ( spl9_32
  <=> m1_subset_1(sK7,k2_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f297,plain,
    ( spl9_36
  <=> m1_subset_1(sK7,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f306,plain,
    ( spl9_37
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f311,plain,
    ( spl9_38
  <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f381,plain,
    ( spl9_41
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f1367,plain,
    ( spl9_160
  <=> m1_pre_topc(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f1550,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1549,f312])).

fof(f312,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f311])).

fof(f1549,plain,
    ( ~ v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ v1_tsep_1(sK4,sK5)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1548,f391])).

fof(f1548,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3))
    | ~ v1_tsep_1(sK4,sK5)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1547,f249])).

fof(f249,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f247])).

fof(f1547,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1546,f307])).

fof(f307,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f306])).

fof(f1546,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1545,f391])).

fof(f1545,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3))))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1544,f249])).

fof(f1544,plain,
    ( ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1543,f299])).

fof(f299,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f297])).

fof(f1543,plain,
    ( ~ m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1542,f391])).

fof(f1542,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_32
    | ~ spl9_41
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1541,f280])).

fof(f280,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f1541,plain,
    ( ~ m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_41
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1540,f383])).

fof(f383,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f381])).

fof(f1540,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1539,f197])).

fof(f197,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f1539,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1538,f192])).

fof(f192,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f1538,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1537,f187])).

fof(f187,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1537,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1536,f182])).

fof(f182,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1536,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1535,f177])).

fof(f177,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1535,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1534,f172])).

fof(f172,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1534,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1533,f167])).

fof(f167,plain,
    ( ~ v2_struct_0(sK4)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1533,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1532,f162])).

fof(f162,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1532,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1531,f157])).

fof(f157,plain,
    ( ~ v2_struct_0(sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1531,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1530,f152])).

fof(f152,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1530,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1529,f147])).

fof(f147,plain,
    ( v1_funct_1(sK6)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1529,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_21
    | ~ spl9_160 ),
    inference(subsumption_resolution,[],[f1528,f1369])).

fof(f1369,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_160 ),
    inference(avatar_component_clause,[],[f1367])).

fof(f1528,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK4,sK5)
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl9_1
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1527,f107])).

fof(f107,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1527,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_pre_topc(sK4,sK5)
    | ~ v1_tsep_1(sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_21 ),
    inference(resolution,[],[f101,f211])).

fof(f211,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f209])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f1525,plain,
    ( spl9_180
    | ~ spl9_181
    | ~ spl9_169 ),
    inference(avatar_split_clause,[],[f1515,f1435,f1522,f1518])).

fof(f1435,plain,
    ( spl9_169
  <=> sP1(sK5,k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_169])])).

fof(f1515,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK5)
    | sP0(sK5,sK4)
    | ~ spl9_169 ),
    inference(resolution,[],[f1437,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1437,plain,
    ( sP1(sK5,k2_struct_0(sK4),sK4)
    | ~ spl9_169 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1455,plain,
    ( spl9_170
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f1449,f1367,f389,f381,f326,f1452])).

fof(f326,plain,
    ( spl9_40
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f1449,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1448,f383])).

fof(f1448,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ spl9_40
    | ~ spl9_42
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1415,f391])).

fof(f1415,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl9_40
    | ~ spl9_160 ),
    inference(unit_resulting_resolution,[],[f327,f1369,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f327,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f326])).

fof(f1438,plain,
    ( spl9_169
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_48
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f1433,f1367,f444,f381,f326,f1435])).

fof(f444,plain,
    ( spl9_48
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f1433,plain,
    ( sP1(sK5,k2_struct_0(sK4),sK4)
    | ~ spl9_40
    | ~ spl9_41
    | ~ spl9_48
    | ~ spl9_160 ),
    inference(forward_demodulation,[],[f1430,f383])).

fof(f1430,plain,
    ( sP1(sK5,u1_struct_0(sK4),sK4)
    | ~ spl9_40
    | ~ spl9_48
    | ~ spl9_160 ),
    inference(unit_resulting_resolution,[],[f446,f327,f1369,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f103,f82])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f42,f44,f43])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f446,plain,
    ( v2_pre_topc(sK5)
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1370,plain,
    ( spl9_160
    | spl9_13
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_123 ),
    inference(avatar_split_clause,[],[f1365,f1110,f439,f399,f318,f165,f1367])).

fof(f399,plain,
    ( spl9_43
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f439,plain,
    ( spl9_47
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f1110,plain,
    ( spl9_123
  <=> sK5 = k1_tsep_1(sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f1365,plain,
    ( m1_pre_topc(sK4,sK5)
    | spl9_13
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_123 ),
    inference(forward_demodulation,[],[f1338,f1112])).

fof(f1112,plain,
    ( sK5 = k1_tsep_1(sK4,sK4,sK4)
    | ~ spl9_123 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f1338,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK4,sK4,sK4))
    | spl9_13
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f167,f441,f319,f167,f401,f167,f401,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f401,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f399])).

fof(f441,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f439])).

fof(f1113,plain,
    ( spl9_123
    | spl9_13
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f1108,f439,f399,f381,f318,f273,f165,f1110])).

fof(f273,plain,
    ( spl9_31
  <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f1108,plain,
    ( sK5 = k1_tsep_1(sK4,sK4,sK4)
    | spl9_13
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f1107,f275])).

fof(f275,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f1107,plain,
    ( g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK4,sK4,sK4)
    | spl9_13
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f1083,f383])).

fof(f1083,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK4,sK4,sK4)
    | spl9_13
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f167,f441,f319,f167,f401,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f618,plain,
    ( spl9_66
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f613,f399,f381,f318,f273,f615])).

fof(f613,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f612,f275])).

fof(f612,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),sK4)
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f595,f383])).

fof(f595,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4)
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(unit_resulting_resolution,[],[f319,f401,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f460,plain,
    ( spl9_49
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f455,f439,f318,f457])).

fof(f455,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f319,f441,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f453,plain,
    ( spl9_47
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f452,f190,f185,f160,f439])).

fof(f452,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f451,f192])).

fof(f451,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f432,f187])).

fof(f432,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12 ),
    inference(resolution,[],[f92,f162])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f450,plain,
    ( spl9_48
    | ~ spl9_10
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f449,f190,f185,f150,f444])).

fof(f449,plain,
    ( v2_pre_topc(sK5)
    | ~ spl9_10
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f448,f192])).

fof(f448,plain,
    ( v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f431,f187])).

fof(f431,plain,
    ( v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_10 ),
    inference(resolution,[],[f92,f152])).

fof(f402,plain,
    ( spl9_43
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f396,f318,f399])).

fof(f396,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f319,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f392,plain,
    ( spl9_42
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f387,f283,f389])).

fof(f283,plain,
    ( spl9_33
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f387,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f284,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f284,plain,
    ( l1_struct_0(sK5)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f384,plain,
    ( spl9_41
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f379,f269,f381])).

fof(f269,plain,
    ( spl9_30
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f379,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f270,f78])).

fof(f270,plain,
    ( l1_struct_0(sK4)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f269])).

fof(f376,plain,
    ( spl9_40
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f335,f185,f150,f326])).

fof(f335,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f187,f152,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f373,plain,
    ( spl9_39
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f338,f185,f160,f318])).

fof(f338,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f187,f162,f81])).

fof(f370,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f369,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f330,plain,
    ( ~ spl9_40
    | spl9_33 ),
    inference(avatar_split_clause,[],[f324,f283,f326])).

fof(f324,plain,
    ( ~ l1_pre_topc(sK5)
    | spl9_33 ),
    inference(resolution,[],[f285,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f285,plain,
    ( ~ l1_struct_0(sK5)
    | spl9_33 ),
    inference(avatar_component_clause,[],[f283])).

fof(f322,plain,
    ( ~ spl9_39
    | spl9_30 ),
    inference(avatar_split_clause,[],[f316,f269,f318])).

fof(f316,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_30 ),
    inference(resolution,[],[f271,f79])).

fof(f271,plain,
    ( ~ l1_struct_0(sK4)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f269])).

fof(f300,plain,
    ( ~ spl9_33
    | spl9_36
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f245,f125,f297,f283])).

fof(f125,plain,
    ( spl9_5
  <=> m1_subset_1(sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f245,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl9_5 ),
    inference(superposition,[],[f127,f78])).

fof(f127,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f295,plain,
    ( ~ spl9_33
    | spl9_35
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f244,f140,f292,f283])).

fof(f292,plain,
    ( spl9_35
  <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f140,plain,
    ( spl9_8
  <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f244,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ spl9_8 ),
    inference(superposition,[],[f142,f78])).

fof(f142,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f290,plain,
    ( ~ spl9_33
    | spl9_34
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f243,f135,f287,f283])).

fof(f287,plain,
    ( spl9_34
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f135,plain,
    ( spl9_7
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f243,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ spl9_7 ),
    inference(superposition,[],[f137,f78])).

fof(f137,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f281,plain,
    ( ~ spl9_30
    | spl9_32
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f242,f203,f278,f269])).

fof(f203,plain,
    ( spl9_20
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f242,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_20 ),
    inference(superposition,[],[f205,f78])).

fof(f205,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f276,plain,
    ( ~ spl9_30
    | spl9_31
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f241,f130,f273,f269])).

fof(f130,plain,
    ( spl9_6
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f241,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_6 ),
    inference(superposition,[],[f132,f78])).

fof(f132,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f250,plain,
    ( spl9_26
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f238,f221,f247])).

fof(f221,plain,
    ( spl9_23
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f238,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f223,f78])).

fof(f223,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( spl9_23
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f213,f170,f221])).

fof(f213,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f172,f79])).

fof(f212,plain,
    ( spl9_21
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f207,f115,f110,f209])).

fof(f110,plain,
    ( spl9_2
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f115,plain,
    ( spl9_3
  <=> sK7 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f207,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f112,f117])).

fof(f117,plain,
    ( sK7 = sK8
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f112,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f206,plain,
    ( spl9_20
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f201,f120,f115,f203])).

fof(f120,plain,
    ( spl9_4
  <=> m1_subset_1(sK8,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f201,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f122,f117])).

fof(f122,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f198,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f59,f195])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f52,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK3,X4,X5)
                          & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK3,X4,X5)
                        & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK3,X4,X5)
                      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK3,X4,X5)
                    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                  & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
              & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
            & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
          & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
        & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f193,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f60,f190])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f188,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f61,f185])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f183,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f62,f180])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f178,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f63,f175])).

fof(f63,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f173,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f64,f170])).

fof(f64,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f168,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f65,f165])).

fof(f65,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f163,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f66,f160])).

fof(f66,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f158,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f67,f155])).

fof(f67,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f153,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f68,f150])).

fof(f68,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f148,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f69,f145])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f143,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f70,f140])).

fof(f70,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f138,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f71,f135])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f133,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f72,f130])).

fof(f72,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f53])).

fof(f128,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f73,f125])).

fof(f73,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f123,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f74,f120])).

fof(f74,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f75,f115])).

fof(f75,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f76,f110])).

fof(f76,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f77,f105])).

fof(f77,plain,(
    ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.47  % (21743)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.49  % (21751)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.49  % (21747)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.49  % (21739)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.50  % (21742)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (21738)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.50  % (21752)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.50  % (21748)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.50  % (21744)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.50  % (21737)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.50  % (21741)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.50  % (21749)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (21740)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.51  % (21750)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.51  % (21745)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.51  % (21755)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.51  % (21754)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.51  % (21753)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.51  % (21746)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.52  % (21738)Refutation not found, incomplete strategy% (21738)------------------------------
% 0.23/0.52  % (21738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (21738)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (21738)Memory used [KB]: 10746
% 0.23/0.52  % (21738)Time elapsed: 0.085 s
% 0.23/0.52  % (21738)------------------------------
% 0.23/0.52  % (21738)------------------------------
% 0.23/0.52  % (21757)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.53  % (21756)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.42/0.55  % (21753)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f1578,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f198,f206,f212,f224,f250,f276,f281,f290,f295,f300,f322,f330,f369,f370,f373,f376,f384,f392,f402,f450,f453,f460,f618,f1113,f1370,f1438,f1455,f1525,f1555,f1576,f1577])).
% 1.42/0.55  fof(f1577,plain,(
% 1.42/0.55    ~spl9_180 | spl9_182),
% 1.42/0.55    inference(avatar_split_clause,[],[f1556,f1552,f1518])).
% 1.42/0.55  fof(f1518,plain,(
% 1.42/0.55    spl9_180 <=> sP0(sK5,sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).
% 1.42/0.55  fof(f1552,plain,(
% 1.42/0.55    spl9_182 <=> v1_tsep_1(sK4,sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).
% 1.42/0.55  fof(f1556,plain,(
% 1.42/0.55    ~sP0(sK5,sK4) | spl9_182),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f1554,f96])).
% 1.42/0.55  fof(f96,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tsep_1(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f58])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.42/0.55    inference(flattening,[],[f57])).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 1.42/0.55    inference(nnf_transformation,[],[f43])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 1.42/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.55  fof(f1554,plain,(
% 1.42/0.55    ~v1_tsep_1(sK4,sK5) | spl9_182),
% 1.42/0.55    inference(avatar_component_clause,[],[f1552])).
% 1.42/0.55  fof(f1576,plain,(
% 1.42/0.55    ~spl9_39 | ~spl9_42 | ~spl9_49 | ~spl9_66 | ~spl9_170 | spl9_181),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f1575])).
% 1.42/0.55  fof(f1575,plain,(
% 1.42/0.55    $false | (~spl9_39 | ~spl9_42 | ~spl9_49 | ~spl9_66 | ~spl9_170 | spl9_181)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1574,f1454])).
% 1.42/0.55  fof(f1454,plain,(
% 1.42/0.55    m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5))) | ~spl9_170),
% 1.42/0.55    inference(avatar_component_clause,[],[f1452])).
% 1.42/0.55  fof(f1452,plain,(
% 1.42/0.55    spl9_170 <=> m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).
% 1.42/0.55  fof(f1574,plain,(
% 1.42/0.55    ~m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5))) | (~spl9_39 | ~spl9_42 | ~spl9_49 | ~spl9_66 | spl9_181)),
% 1.42/0.55    inference(forward_demodulation,[],[f1566,f391])).
% 1.42/0.55  fof(f391,plain,(
% 1.42/0.55    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_42),
% 1.42/0.55    inference(avatar_component_clause,[],[f389])).
% 1.42/0.55  fof(f389,plain,(
% 1.42/0.55    spl9_42 <=> u1_struct_0(sK5) = k2_struct_0(sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.42/0.55  fof(f1566,plain,(
% 1.42/0.55    ~m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) | (~spl9_39 | ~spl9_49 | ~spl9_66 | spl9_181)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f319,f617,f459,f1524,f199])).
% 1.42/0.55  fof(f199,plain,(
% 1.42/0.55    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f100,f85])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f86])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 1.42/0.55  fof(f1524,plain,(
% 1.42/0.55    ~v3_pre_topc(k2_struct_0(sK4),sK5) | spl9_181),
% 1.42/0.55    inference(avatar_component_clause,[],[f1522])).
% 1.42/0.55  fof(f1522,plain,(
% 1.42/0.55    spl9_181 <=> v3_pre_topc(k2_struct_0(sK4),sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_181])])).
% 1.42/0.55  fof(f459,plain,(
% 1.42/0.55    v3_pre_topc(k2_struct_0(sK4),sK4) | ~spl9_49),
% 1.42/0.55    inference(avatar_component_clause,[],[f457])).
% 1.42/0.55  fof(f457,plain,(
% 1.42/0.55    spl9_49 <=> v3_pre_topc(k2_struct_0(sK4),sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 1.42/0.55  fof(f617,plain,(
% 1.42/0.55    m1_pre_topc(sK5,sK4) | ~spl9_66),
% 1.42/0.55    inference(avatar_component_clause,[],[f615])).
% 1.42/0.55  fof(f615,plain,(
% 1.42/0.55    spl9_66 <=> m1_pre_topc(sK5,sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 1.42/0.55  fof(f319,plain,(
% 1.42/0.55    l1_pre_topc(sK4) | ~spl9_39),
% 1.42/0.55    inference(avatar_component_clause,[],[f318])).
% 1.42/0.55  fof(f318,plain,(
% 1.42/0.55    spl9_39 <=> l1_pre_topc(sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 1.42/0.55  fof(f1555,plain,(
% 1.42/0.55    ~spl9_182 | spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_160),
% 1.42/0.55    inference(avatar_split_clause,[],[f1550,f1367,f389,f381,f311,f306,f297,f278,f247,f209,f195,f190,f185,f180,f175,f170,f165,f160,f155,f150,f145,f105,f1552])).
% 1.42/0.55  fof(f105,plain,(
% 1.42/0.55    spl9_1 <=> r1_tmap_1(sK5,sK3,sK6,sK7)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    spl9_9 <=> v1_funct_1(sK6)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.42/0.55  fof(f150,plain,(
% 1.42/0.55    spl9_10 <=> m1_pre_topc(sK5,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.42/0.55  fof(f155,plain,(
% 1.42/0.55    spl9_11 <=> v2_struct_0(sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.42/0.55  fof(f160,plain,(
% 1.42/0.55    spl9_12 <=> m1_pre_topc(sK4,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.42/0.55  fof(f165,plain,(
% 1.42/0.55    spl9_13 <=> v2_struct_0(sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.42/0.55  fof(f170,plain,(
% 1.42/0.55    spl9_14 <=> l1_pre_topc(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.42/0.55  fof(f175,plain,(
% 1.42/0.55    spl9_15 <=> v2_pre_topc(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.42/0.55  fof(f180,plain,(
% 1.42/0.55    spl9_16 <=> v2_struct_0(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.42/0.55  fof(f185,plain,(
% 1.42/0.55    spl9_17 <=> l1_pre_topc(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.42/0.55  fof(f190,plain,(
% 1.42/0.55    spl9_18 <=> v2_pre_topc(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.42/0.55  fof(f195,plain,(
% 1.42/0.55    spl9_19 <=> v2_struct_0(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.42/0.55  fof(f209,plain,(
% 1.42/0.55    spl9_21 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.42/0.55  fof(f247,plain,(
% 1.42/0.55    spl9_26 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.42/0.55  fof(f278,plain,(
% 1.42/0.55    spl9_32 <=> m1_subset_1(sK7,k2_struct_0(sK4))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.42/0.55  fof(f297,plain,(
% 1.42/0.55    spl9_36 <=> m1_subset_1(sK7,k2_struct_0(sK5))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 1.42/0.55  fof(f306,plain,(
% 1.42/0.55    spl9_37 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 1.42/0.55  fof(f311,plain,(
% 1.42/0.55    spl9_38 <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 1.42/0.55  fof(f381,plain,(
% 1.42/0.55    spl9_41 <=> u1_struct_0(sK4) = k2_struct_0(sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 1.42/0.55  fof(f1367,plain,(
% 1.42/0.55    spl9_160 <=> m1_pre_topc(sK4,sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).
% 1.42/0.55  fof(f1550,plain,(
% 1.42/0.55    ~v1_tsep_1(sK4,sK5) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1549,f312])).
% 1.42/0.55  fof(f312,plain,(
% 1.42/0.55    v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~spl9_38),
% 1.42/0.55    inference(avatar_component_clause,[],[f311])).
% 1.42/0.55  fof(f1549,plain,(
% 1.42/0.55    ~v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~v1_tsep_1(sK4,sK5) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1548,f391])).
% 1.42/0.55  fof(f1548,plain,(
% 1.42/0.55    ~v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3)) | ~v1_tsep_1(sK4,sK5) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1547,f249])).
% 1.42/0.55  fof(f249,plain,(
% 1.42/0.55    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_26),
% 1.42/0.55    inference(avatar_component_clause,[],[f247])).
% 1.42/0.55  fof(f1547,plain,(
% 1.42/0.55    ~v1_tsep_1(sK4,sK5) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1546,f307])).
% 1.42/0.55  fof(f307,plain,(
% 1.42/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~spl9_37),
% 1.42/0.55    inference(avatar_component_clause,[],[f306])).
% 1.42/0.55  fof(f1546,plain,(
% 1.42/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~v1_tsep_1(sK4,sK5) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1545,f391])).
% 1.42/0.55  fof(f1545,plain,(
% 1.42/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3)))) | ~v1_tsep_1(sK4,sK5) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1544,f249])).
% 1.42/0.55  fof(f1544,plain,(
% 1.42/0.55    ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_36 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1543,f299])).
% 1.42/0.55  fof(f299,plain,(
% 1.42/0.55    m1_subset_1(sK7,k2_struct_0(sK5)) | ~spl9_36),
% 1.42/0.55    inference(avatar_component_clause,[],[f297])).
% 1.42/0.55  fof(f1543,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,k2_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1542,f391])).
% 1.42/0.55  fof(f1542,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_32 | ~spl9_41 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1541,f280])).
% 1.42/0.55  fof(f280,plain,(
% 1.42/0.55    m1_subset_1(sK7,k2_struct_0(sK4)) | ~spl9_32),
% 1.42/0.55    inference(avatar_component_clause,[],[f278])).
% 1.42/0.55  fof(f1541,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,k2_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_41 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1540,f383])).
% 1.42/0.55  fof(f383,plain,(
% 1.42/0.55    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_41),
% 1.42/0.55    inference(avatar_component_clause,[],[f381])).
% 1.42/0.55  fof(f1540,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1539,f197])).
% 1.42/0.55  fof(f197,plain,(
% 1.42/0.55    ~v2_struct_0(sK2) | spl9_19),
% 1.42/0.55    inference(avatar_component_clause,[],[f195])).
% 1.42/0.55  fof(f1539,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1538,f192])).
% 1.42/0.55  fof(f192,plain,(
% 1.42/0.55    v2_pre_topc(sK2) | ~spl9_18),
% 1.42/0.55    inference(avatar_component_clause,[],[f190])).
% 1.42/0.55  fof(f1538,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1537,f187])).
% 1.42/0.55  fof(f187,plain,(
% 1.42/0.55    l1_pre_topc(sK2) | ~spl9_17),
% 1.42/0.55    inference(avatar_component_clause,[],[f185])).
% 1.42/0.55  fof(f1537,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1536,f182])).
% 1.42/0.55  fof(f182,plain,(
% 1.42/0.55    ~v2_struct_0(sK3) | spl9_16),
% 1.42/0.55    inference(avatar_component_clause,[],[f180])).
% 1.42/0.55  fof(f1536,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1535,f177])).
% 1.42/0.55  fof(f177,plain,(
% 1.42/0.55    v2_pre_topc(sK3) | ~spl9_15),
% 1.42/0.55    inference(avatar_component_clause,[],[f175])).
% 1.42/0.55  fof(f1535,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_14 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1534,f172])).
% 1.42/0.55  fof(f172,plain,(
% 1.42/0.55    l1_pre_topc(sK3) | ~spl9_14),
% 1.42/0.55    inference(avatar_component_clause,[],[f170])).
% 1.42/0.55  fof(f1534,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | spl9_13 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1533,f167])).
% 1.42/0.55  fof(f167,plain,(
% 1.42/0.55    ~v2_struct_0(sK4) | spl9_13),
% 1.42/0.55    inference(avatar_component_clause,[],[f165])).
% 1.42/0.55  fof(f1533,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_12 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1532,f162])).
% 1.42/0.55  fof(f162,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK2) | ~spl9_12),
% 1.42/0.55    inference(avatar_component_clause,[],[f160])).
% 1.42/0.55  fof(f1532,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1531,f157])).
% 1.42/0.55  fof(f157,plain,(
% 1.42/0.55    ~v2_struct_0(sK5) | spl9_11),
% 1.42/0.55    inference(avatar_component_clause,[],[f155])).
% 1.42/0.55  fof(f1531,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1530,f152])).
% 1.42/0.55  fof(f152,plain,(
% 1.42/0.55    m1_pre_topc(sK5,sK2) | ~spl9_10),
% 1.42/0.55    inference(avatar_component_clause,[],[f150])).
% 1.42/0.55  fof(f1530,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_9 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1529,f147])).
% 1.42/0.55  fof(f147,plain,(
% 1.42/0.55    v1_funct_1(sK6) | ~spl9_9),
% 1.42/0.55    inference(avatar_component_clause,[],[f145])).
% 1.42/0.55  fof(f1529,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_21 | ~spl9_160)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1528,f1369])).
% 1.42/0.55  fof(f1369,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK5) | ~spl9_160),
% 1.42/0.55    inference(avatar_component_clause,[],[f1367])).
% 1.42/0.55  fof(f1528,plain,(
% 1.42/0.55    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl9_1 | ~spl9_21)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1527,f107])).
% 1.42/0.55  fof(f107,plain,(
% 1.42/0.55    ~r1_tmap_1(sK5,sK3,sK6,sK7) | spl9_1),
% 1.42/0.55    inference(avatar_component_clause,[],[f105])).
% 1.42/0.55  fof(f1527,plain,(
% 1.42/0.55    r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl9_21),
% 1.42/0.55    inference(resolution,[],[f101,f211])).
% 1.42/0.55  fof(f211,plain,(
% 1.42/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | ~spl9_21),
% 1.42/0.55    inference(avatar_component_clause,[],[f209])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f88])).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f54])).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(nnf_transformation,[],[f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.42/0.55  fof(f1525,plain,(
% 1.42/0.55    spl9_180 | ~spl9_181 | ~spl9_169),
% 1.42/0.55    inference(avatar_split_clause,[],[f1515,f1435,f1522,f1518])).
% 1.42/0.55  fof(f1435,plain,(
% 1.42/0.55    spl9_169 <=> sP1(sK5,k2_struct_0(sK4),sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_169])])).
% 1.42/0.55  fof(f1515,plain,(
% 1.42/0.55    ~v3_pre_topc(k2_struct_0(sK4),sK5) | sP0(sK5,sK4) | ~spl9_169),
% 1.42/0.55    inference(resolution,[],[f1437,f95])).
% 1.42/0.55  fof(f95,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_pre_topc(X1,X0) | sP0(X0,X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f56])).
% 1.42/0.55  fof(f56,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 1.42/0.55    inference(rectify,[],[f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 1.42/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.42/0.55  fof(f1437,plain,(
% 1.42/0.55    sP1(sK5,k2_struct_0(sK4),sK4) | ~spl9_169),
% 1.42/0.55    inference(avatar_component_clause,[],[f1435])).
% 1.42/0.55  fof(f1455,plain,(
% 1.42/0.55    spl9_170 | ~spl9_40 | ~spl9_41 | ~spl9_42 | ~spl9_160),
% 1.42/0.55    inference(avatar_split_clause,[],[f1449,f1367,f389,f381,f326,f1452])).
% 1.42/0.55  fof(f326,plain,(
% 1.42/0.55    spl9_40 <=> l1_pre_topc(sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 1.42/0.55  fof(f1449,plain,(
% 1.42/0.55    m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5))) | (~spl9_40 | ~spl9_41 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1448,f383])).
% 1.42/0.55  fof(f1448,plain,(
% 1.42/0.55    m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK5))) | (~spl9_40 | ~spl9_42 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1415,f391])).
% 1.42/0.55  fof(f1415,plain,(
% 1.42/0.55    m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) | (~spl9_40 | ~spl9_160)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f327,f1369,f82])).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.42/0.55  fof(f327,plain,(
% 1.42/0.55    l1_pre_topc(sK5) | ~spl9_40),
% 1.42/0.55    inference(avatar_component_clause,[],[f326])).
% 1.42/0.55  fof(f1438,plain,(
% 1.42/0.55    spl9_169 | ~spl9_40 | ~spl9_41 | ~spl9_48 | ~spl9_160),
% 1.42/0.55    inference(avatar_split_clause,[],[f1433,f1367,f444,f381,f326,f1435])).
% 1.42/0.55  fof(f444,plain,(
% 1.42/0.55    spl9_48 <=> v2_pre_topc(sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 1.42/0.55  fof(f1433,plain,(
% 1.42/0.55    sP1(sK5,k2_struct_0(sK4),sK4) | (~spl9_40 | ~spl9_41 | ~spl9_48 | ~spl9_160)),
% 1.42/0.55    inference(forward_demodulation,[],[f1430,f383])).
% 1.42/0.55  fof(f1430,plain,(
% 1.42/0.55    sP1(sK5,u1_struct_0(sK4),sK4) | (~spl9_40 | ~spl9_48 | ~spl9_160)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f446,f327,f1369,f200])).
% 1.42/0.55  fof(f200,plain,(
% 1.42/0.55    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f103,f82])).
% 1.42/0.55  fof(f103,plain,(
% 1.42/0.55    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f99])).
% 1.42/0.55  fof(f99,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.55    inference(definition_folding,[],[f42,f44,f43])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f41])).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.42/0.55  fof(f446,plain,(
% 1.42/0.55    v2_pre_topc(sK5) | ~spl9_48),
% 1.42/0.55    inference(avatar_component_clause,[],[f444])).
% 1.42/0.55  fof(f1370,plain,(
% 1.42/0.55    spl9_160 | spl9_13 | ~spl9_39 | ~spl9_43 | ~spl9_47 | ~spl9_123),
% 1.42/0.55    inference(avatar_split_clause,[],[f1365,f1110,f439,f399,f318,f165,f1367])).
% 1.42/0.55  fof(f399,plain,(
% 1.42/0.55    spl9_43 <=> m1_pre_topc(sK4,sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 1.42/0.55  fof(f439,plain,(
% 1.42/0.55    spl9_47 <=> v2_pre_topc(sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 1.42/0.55  fof(f1110,plain,(
% 1.42/0.55    spl9_123 <=> sK5 = k1_tsep_1(sK4,sK4,sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).
% 1.42/0.55  fof(f1365,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK5) | (spl9_13 | ~spl9_39 | ~spl9_43 | ~spl9_47 | ~spl9_123)),
% 1.42/0.55    inference(forward_demodulation,[],[f1338,f1112])).
% 1.42/0.55  fof(f1112,plain,(
% 1.42/0.55    sK5 = k1_tsep_1(sK4,sK4,sK4) | ~spl9_123),
% 1.42/0.55    inference(avatar_component_clause,[],[f1110])).
% 1.42/0.55  fof(f1338,plain,(
% 1.42/0.55    m1_pre_topc(sK4,k1_tsep_1(sK4,sK4,sK4)) | (spl9_13 | ~spl9_39 | ~spl9_43 | ~spl9_47)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f167,f441,f319,f167,f401,f167,f401,f90])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f33])).
% 1.42/0.55  fof(f33,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 1.42/0.55  fof(f401,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK4) | ~spl9_43),
% 1.42/0.55    inference(avatar_component_clause,[],[f399])).
% 1.42/0.55  fof(f441,plain,(
% 1.42/0.55    v2_pre_topc(sK4) | ~spl9_47),
% 1.42/0.55    inference(avatar_component_clause,[],[f439])).
% 1.42/0.55  fof(f1113,plain,(
% 1.42/0.55    spl9_123 | spl9_13 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47),
% 1.42/0.55    inference(avatar_split_clause,[],[f1108,f439,f399,f381,f318,f273,f165,f1110])).
% 1.42/0.55  fof(f273,plain,(
% 1.42/0.55    spl9_31 <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.42/0.55  fof(f1108,plain,(
% 1.42/0.55    sK5 = k1_tsep_1(sK4,sK4,sK4) | (spl9_13 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47)),
% 1.42/0.55    inference(forward_demodulation,[],[f1107,f275])).
% 1.42/0.55  fof(f275,plain,(
% 1.42/0.55    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~spl9_31),
% 1.42/0.55    inference(avatar_component_clause,[],[f273])).
% 1.42/0.55  fof(f1107,plain,(
% 1.42/0.55    g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK4,sK4,sK4) | (spl9_13 | ~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47)),
% 1.42/0.55    inference(forward_demodulation,[],[f1083,f383])).
% 1.42/0.55  fof(f1083,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK4,sK4,sK4) | (spl9_13 | ~spl9_39 | ~spl9_43 | ~spl9_47)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f167,f441,f319,f167,f401,f89])).
% 1.42/0.55  fof(f89,plain,(
% 1.42/0.55    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 1.42/0.55  fof(f618,plain,(
% 1.42/0.55    spl9_66 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43),
% 1.42/0.55    inference(avatar_split_clause,[],[f613,f399,f381,f318,f273,f615])).
% 1.42/0.55  fof(f613,plain,(
% 1.42/0.55    m1_pre_topc(sK5,sK4) | (~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43)),
% 1.42/0.55    inference(forward_demodulation,[],[f612,f275])).
% 1.42/0.55  fof(f612,plain,(
% 1.42/0.55    m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),sK4) | (~spl9_39 | ~spl9_41 | ~spl9_43)),
% 1.42/0.55    inference(forward_demodulation,[],[f595,f383])).
% 1.42/0.55  fof(f595,plain,(
% 1.42/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK4) | (~spl9_39 | ~spl9_43)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f319,f401,f84])).
% 1.42/0.55  fof(f84,plain,(
% 1.42/0.55    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.42/0.55  fof(f460,plain,(
% 1.42/0.55    spl9_49 | ~spl9_39 | ~spl9_47),
% 1.42/0.55    inference(avatar_split_clause,[],[f455,f439,f318,f457])).
% 1.42/0.55  fof(f455,plain,(
% 1.42/0.55    v3_pre_topc(k2_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_47)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f319,f441,f91])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f36])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.42/0.55  fof(f453,plain,(
% 1.42/0.55    spl9_47 | ~spl9_12 | ~spl9_17 | ~spl9_18),
% 1.42/0.55    inference(avatar_split_clause,[],[f452,f190,f185,f160,f439])).
% 1.42/0.55  fof(f452,plain,(
% 1.42/0.55    v2_pre_topc(sK4) | (~spl9_12 | ~spl9_17 | ~spl9_18)),
% 1.42/0.55    inference(subsumption_resolution,[],[f451,f192])).
% 1.42/0.55  fof(f451,plain,(
% 1.42/0.55    v2_pre_topc(sK4) | ~v2_pre_topc(sK2) | (~spl9_12 | ~spl9_17)),
% 1.42/0.55    inference(subsumption_resolution,[],[f432,f187])).
% 1.42/0.55  fof(f432,plain,(
% 1.42/0.55    v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl9_12),
% 1.42/0.55    inference(resolution,[],[f92,f162])).
% 1.42/0.55  fof(f92,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f38])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.55    inference(flattening,[],[f37])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.42/0.55  fof(f450,plain,(
% 1.42/0.55    spl9_48 | ~spl9_10 | ~spl9_17 | ~spl9_18),
% 1.42/0.55    inference(avatar_split_clause,[],[f449,f190,f185,f150,f444])).
% 1.42/0.55  fof(f449,plain,(
% 1.42/0.55    v2_pre_topc(sK5) | (~spl9_10 | ~spl9_17 | ~spl9_18)),
% 1.42/0.55    inference(subsumption_resolution,[],[f448,f192])).
% 1.42/0.55  fof(f448,plain,(
% 1.42/0.55    v2_pre_topc(sK5) | ~v2_pre_topc(sK2) | (~spl9_10 | ~spl9_17)),
% 1.42/0.55    inference(subsumption_resolution,[],[f431,f187])).
% 1.42/0.55  fof(f431,plain,(
% 1.42/0.55    v2_pre_topc(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl9_10),
% 1.42/0.55    inference(resolution,[],[f92,f152])).
% 1.42/0.55  fof(f402,plain,(
% 1.42/0.55    spl9_43 | ~spl9_39),
% 1.42/0.55    inference(avatar_split_clause,[],[f396,f318,f399])).
% 1.42/0.55  fof(f396,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK4) | ~spl9_39),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f319,f80])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.42/0.55  fof(f392,plain,(
% 1.42/0.55    spl9_42 | ~spl9_33),
% 1.42/0.55    inference(avatar_split_clause,[],[f387,f283,f389])).
% 1.42/0.55  fof(f283,plain,(
% 1.42/0.55    spl9_33 <=> l1_struct_0(sK5)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 1.42/0.55  fof(f387,plain,(
% 1.42/0.55    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_33),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f284,f78])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.42/0.55  fof(f284,plain,(
% 1.42/0.55    l1_struct_0(sK5) | ~spl9_33),
% 1.42/0.55    inference(avatar_component_clause,[],[f283])).
% 1.42/0.55  fof(f384,plain,(
% 1.42/0.55    spl9_41 | ~spl9_30),
% 1.42/0.55    inference(avatar_split_clause,[],[f379,f269,f381])).
% 1.42/0.55  fof(f269,plain,(
% 1.42/0.55    spl9_30 <=> l1_struct_0(sK4)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.42/0.55  fof(f379,plain,(
% 1.42/0.55    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_30),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f270,f78])).
% 1.42/0.55  fof(f270,plain,(
% 1.42/0.55    l1_struct_0(sK4) | ~spl9_30),
% 1.42/0.55    inference(avatar_component_clause,[],[f269])).
% 1.42/0.55  fof(f376,plain,(
% 1.42/0.55    spl9_40 | ~spl9_10 | ~spl9_17),
% 1.42/0.55    inference(avatar_split_clause,[],[f335,f185,f150,f326])).
% 1.42/0.55  fof(f335,plain,(
% 1.42/0.55    l1_pre_topc(sK5) | (~spl9_10 | ~spl9_17)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f187,f152,f81])).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.42/0.55  fof(f373,plain,(
% 1.42/0.55    spl9_39 | ~spl9_12 | ~spl9_17),
% 1.42/0.55    inference(avatar_split_clause,[],[f338,f185,f160,f318])).
% 1.42/0.55  fof(f338,plain,(
% 1.42/0.55    l1_pre_topc(sK4) | (~spl9_12 | ~spl9_17)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f187,f162,f81])).
% 1.42/0.55  fof(f370,plain,(
% 1.42/0.55    u1_struct_0(sK3) != k2_struct_0(sK3) | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 1.42/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.42/0.55  fof(f369,plain,(
% 1.42/0.55    u1_struct_0(sK3) != k2_struct_0(sK3) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 1.42/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.42/0.55  fof(f330,plain,(
% 1.42/0.55    ~spl9_40 | spl9_33),
% 1.42/0.55    inference(avatar_split_clause,[],[f324,f283,f326])).
% 1.42/0.55  fof(f324,plain,(
% 1.42/0.55    ~l1_pre_topc(sK5) | spl9_33),
% 1.42/0.55    inference(resolution,[],[f285,f79])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.42/0.55  fof(f285,plain,(
% 1.42/0.55    ~l1_struct_0(sK5) | spl9_33),
% 1.42/0.55    inference(avatar_component_clause,[],[f283])).
% 1.42/0.55  fof(f322,plain,(
% 1.42/0.55    ~spl9_39 | spl9_30),
% 1.42/0.55    inference(avatar_split_clause,[],[f316,f269,f318])).
% 1.42/0.55  fof(f316,plain,(
% 1.42/0.55    ~l1_pre_topc(sK4) | spl9_30),
% 1.42/0.55    inference(resolution,[],[f271,f79])).
% 1.42/0.55  fof(f271,plain,(
% 1.42/0.55    ~l1_struct_0(sK4) | spl9_30),
% 1.42/0.55    inference(avatar_component_clause,[],[f269])).
% 1.42/0.55  fof(f300,plain,(
% 1.42/0.55    ~spl9_33 | spl9_36 | ~spl9_5),
% 1.42/0.55    inference(avatar_split_clause,[],[f245,f125,f297,f283])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    spl9_5 <=> m1_subset_1(sK7,u1_struct_0(sK5))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.42/0.55  fof(f245,plain,(
% 1.42/0.55    m1_subset_1(sK7,k2_struct_0(sK5)) | ~l1_struct_0(sK5) | ~spl9_5),
% 1.42/0.55    inference(superposition,[],[f127,f78])).
% 1.42/0.55  fof(f127,plain,(
% 1.42/0.55    m1_subset_1(sK7,u1_struct_0(sK5)) | ~spl9_5),
% 1.42/0.55    inference(avatar_component_clause,[],[f125])).
% 1.42/0.55  fof(f295,plain,(
% 1.42/0.55    ~spl9_33 | spl9_35 | ~spl9_8),
% 1.42/0.55    inference(avatar_split_clause,[],[f244,f140,f292,f283])).
% 1.42/0.55  fof(f292,plain,(
% 1.42/0.55    spl9_35 <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 1.42/0.55  fof(f140,plain,(
% 1.42/0.55    spl9_8 <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.42/0.55  fof(f244,plain,(
% 1.42/0.55    v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK5) | ~spl9_8),
% 1.42/0.55    inference(superposition,[],[f142,f78])).
% 1.42/0.55  fof(f142,plain,(
% 1.42/0.55    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl9_8),
% 1.42/0.55    inference(avatar_component_clause,[],[f140])).
% 1.42/0.55  fof(f290,plain,(
% 1.42/0.55    ~spl9_33 | spl9_34 | ~spl9_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f243,f135,f287,f283])).
% 1.42/0.55  fof(f287,plain,(
% 1.42/0.55    spl9_34 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 1.42/0.55  fof(f135,plain,(
% 1.42/0.55    spl9_7 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.42/0.55  fof(f243,plain,(
% 1.42/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) | ~l1_struct_0(sK5) | ~spl9_7),
% 1.42/0.55    inference(superposition,[],[f137,f78])).
% 1.42/0.55  fof(f137,plain,(
% 1.42/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl9_7),
% 1.42/0.55    inference(avatar_component_clause,[],[f135])).
% 1.42/0.55  fof(f281,plain,(
% 1.42/0.55    ~spl9_30 | spl9_32 | ~spl9_20),
% 1.42/0.55    inference(avatar_split_clause,[],[f242,f203,f278,f269])).
% 1.42/0.55  fof(f203,plain,(
% 1.42/0.55    spl9_20 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.42/0.55  fof(f242,plain,(
% 1.42/0.55    m1_subset_1(sK7,k2_struct_0(sK4)) | ~l1_struct_0(sK4) | ~spl9_20),
% 1.42/0.55    inference(superposition,[],[f205,f78])).
% 1.42/0.55  fof(f205,plain,(
% 1.42/0.55    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl9_20),
% 1.42/0.55    inference(avatar_component_clause,[],[f203])).
% 1.42/0.55  fof(f276,plain,(
% 1.42/0.55    ~spl9_30 | spl9_31 | ~spl9_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f241,f130,f273,f269])).
% 1.42/0.55  fof(f130,plain,(
% 1.42/0.55    spl9_6 <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.42/0.55  fof(f241,plain,(
% 1.42/0.55    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_struct_0(sK4) | ~spl9_6),
% 1.42/0.55    inference(superposition,[],[f132,f78])).
% 1.42/0.55  fof(f132,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 | ~spl9_6),
% 1.42/0.55    inference(avatar_component_clause,[],[f130])).
% 1.42/0.55  fof(f250,plain,(
% 1.42/0.55    spl9_26 | ~spl9_23),
% 1.42/0.55    inference(avatar_split_clause,[],[f238,f221,f247])).
% 1.42/0.55  fof(f221,plain,(
% 1.42/0.55    spl9_23 <=> l1_struct_0(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.42/0.55  fof(f238,plain,(
% 1.42/0.55    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_23),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f223,f78])).
% 1.42/0.55  fof(f223,plain,(
% 1.42/0.55    l1_struct_0(sK3) | ~spl9_23),
% 1.42/0.55    inference(avatar_component_clause,[],[f221])).
% 1.42/0.55  fof(f224,plain,(
% 1.42/0.55    spl9_23 | ~spl9_14),
% 1.42/0.55    inference(avatar_split_clause,[],[f213,f170,f221])).
% 1.42/0.55  fof(f213,plain,(
% 1.42/0.55    l1_struct_0(sK3) | ~spl9_14),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f172,f79])).
% 1.42/0.55  fof(f212,plain,(
% 1.42/0.55    spl9_21 | ~spl9_2 | ~spl9_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f207,f115,f110,f209])).
% 1.42/0.55  fof(f110,plain,(
% 1.42/0.55    spl9_2 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    spl9_3 <=> sK7 = sK8),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.42/0.55  fof(f207,plain,(
% 1.42/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | (~spl9_2 | ~spl9_3)),
% 1.42/0.55    inference(forward_demodulation,[],[f112,f117])).
% 1.42/0.55  fof(f117,plain,(
% 1.42/0.55    sK7 = sK8 | ~spl9_3),
% 1.42/0.55    inference(avatar_component_clause,[],[f115])).
% 1.42/0.55  fof(f112,plain,(
% 1.42/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~spl9_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f110])).
% 1.42/0.55  fof(f206,plain,(
% 1.42/0.55    spl9_20 | ~spl9_3 | ~spl9_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f201,f120,f115,f203])).
% 1.42/0.55  fof(f120,plain,(
% 1.42/0.55    spl9_4 <=> m1_subset_1(sK8,u1_struct_0(sK4))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.42/0.55  fof(f201,plain,(
% 1.42/0.55    m1_subset_1(sK7,u1_struct_0(sK4)) | (~spl9_3 | ~spl9_4)),
% 1.42/0.55    inference(backward_demodulation,[],[f122,f117])).
% 1.42/0.55  fof(f122,plain,(
% 1.42/0.55    m1_subset_1(sK8,u1_struct_0(sK4)) | ~spl9_4),
% 1.42/0.55    inference(avatar_component_clause,[],[f120])).
% 1.42/0.55  fof(f198,plain,(
% 1.42/0.55    ~spl9_19),
% 1.42/0.55    inference(avatar_split_clause,[],[f59,f195])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    ~v2_struct_0(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ((((((~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f52,f51,f50,f49,f48,f47,f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    ? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.42/0.55    inference(flattening,[],[f18])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f17])).
% 1.42/0.55  fof(f17,negated_conjecture,(
% 1.42/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.42/0.55    inference(negated_conjecture,[],[f16])).
% 1.42/0.55  fof(f16,conjecture,(
% 1.42/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.42/0.55  fof(f193,plain,(
% 1.42/0.55    spl9_18),
% 1.42/0.55    inference(avatar_split_clause,[],[f60,f190])).
% 1.42/0.55  fof(f60,plain,(
% 1.42/0.55    v2_pre_topc(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f188,plain,(
% 1.42/0.55    spl9_17),
% 1.42/0.55    inference(avatar_split_clause,[],[f61,f185])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    l1_pre_topc(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f183,plain,(
% 1.42/0.55    ~spl9_16),
% 1.42/0.55    inference(avatar_split_clause,[],[f62,f180])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ~v2_struct_0(sK3)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f178,plain,(
% 1.42/0.55    spl9_15),
% 1.42/0.55    inference(avatar_split_clause,[],[f63,f175])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    v2_pre_topc(sK3)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f173,plain,(
% 1.42/0.55    spl9_14),
% 1.42/0.55    inference(avatar_split_clause,[],[f64,f170])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    l1_pre_topc(sK3)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f168,plain,(
% 1.42/0.55    ~spl9_13),
% 1.42/0.55    inference(avatar_split_clause,[],[f65,f165])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ~v2_struct_0(sK4)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f163,plain,(
% 1.42/0.55    spl9_12),
% 1.42/0.55    inference(avatar_split_clause,[],[f66,f160])).
% 1.42/0.55  fof(f66,plain,(
% 1.42/0.55    m1_pre_topc(sK4,sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f158,plain,(
% 1.42/0.55    ~spl9_11),
% 1.42/0.55    inference(avatar_split_clause,[],[f67,f155])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    ~v2_struct_0(sK5)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f153,plain,(
% 1.42/0.55    spl9_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f68,f150])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    m1_pre_topc(sK5,sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f148,plain,(
% 1.42/0.55    spl9_9),
% 1.42/0.55    inference(avatar_split_clause,[],[f69,f145])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    v1_funct_1(sK6)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f143,plain,(
% 1.42/0.55    spl9_8),
% 1.42/0.55    inference(avatar_split_clause,[],[f70,f140])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f138,plain,(
% 1.42/0.55    spl9_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f71,f135])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f133,plain,(
% 1.42/0.55    spl9_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f72,f130])).
% 1.42/0.55  fof(f72,plain,(
% 1.42/0.55    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    spl9_5),
% 1.42/0.55    inference(avatar_split_clause,[],[f73,f125])).
% 1.42/0.55  fof(f73,plain,(
% 1.42/0.55    m1_subset_1(sK7,u1_struct_0(sK5))),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f123,plain,(
% 1.42/0.55    spl9_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f74,f120])).
% 1.42/0.55  fof(f74,plain,(
% 1.42/0.55    m1_subset_1(sK8,u1_struct_0(sK4))),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f118,plain,(
% 1.42/0.55    spl9_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f75,f115])).
% 1.42/0.55  fof(f75,plain,(
% 1.42/0.55    sK7 = sK8),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f113,plain,(
% 1.42/0.55    spl9_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f76,f110])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  fof(f108,plain,(
% 1.42/0.55    ~spl9_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f77,f105])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 1.42/0.55    inference(cnf_transformation,[],[f53])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (21753)------------------------------
% 1.42/0.55  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (21753)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (21753)Memory used [KB]: 11897
% 1.42/0.55  % (21753)Time elapsed: 0.134 s
% 1.42/0.55  % (21753)------------------------------
% 1.42/0.55  % (21753)------------------------------
% 1.42/0.56  % (21737)Refutation not found, incomplete strategy% (21737)------------------------------
% 1.42/0.56  % (21737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (21737)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (21737)Memory used [KB]: 6780
% 1.42/0.56  % (21737)Time elapsed: 0.109 s
% 1.42/0.56  % (21737)------------------------------
% 1.42/0.56  % (21737)------------------------------
% 1.56/0.57  % (21736)Success in time 0.2 s
%------------------------------------------------------------------------------
