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
% DateTime   : Thu Dec  3 13:19:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  398 (1066 expanded)
%              Number of leaves         :   69 ( 510 expanded)
%              Depth                    :   18
%              Number of atoms          : 3096 (6980 expanded)
%              Number of equality atoms :   97 ( 369 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f820,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f158,f168,f175,f199,f224,f234,f238,f254,f259,f263,f268,f291,f317,f331,f336,f349,f353,f376,f380,f403,f415,f432,f453,f458,f463,f530,f600,f609,f672,f673,f689,f718,f729,f734,f766,f780,f801,f807,f814,f819])).

fof(f819,plain,
    ( ~ spl5_6
    | spl5_73 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl5_6
    | spl5_73 ),
    inference(subsumption_resolution,[],[f816,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f816,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_73 ),
    inference(resolution,[],[f813,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f813,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_73 ),
    inference(avatar_component_clause,[],[f811])).

fof(f811,plain,
    ( spl5_73
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f814,plain,
    ( ~ spl5_73
    | spl5_4
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f809,f186,f92,f811])).

fof(f92,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f186,plain,
    ( spl5_21
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f809,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_4
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f808,f94])).

fof(f94,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f808,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_21 ),
    inference(resolution,[],[f188,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f188,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f807,plain,
    ( spl5_21
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | spl5_72 ),
    inference(avatar_split_clause,[],[f806,f798,f142,f137,f117,f186])).

fof(f117,plain,
    ( spl5_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f137,plain,
    ( spl5_13
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f142,plain,
    ( spl5_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f798,plain,
    ( spl5_72
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f806,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | spl5_72 ),
    inference(subsumption_resolution,[],[f805,f119])).

fof(f119,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f805,plain,
    ( ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_13
    | ~ spl5_14
    | spl5_72 ),
    inference(subsumption_resolution,[],[f804,f139])).

fof(f139,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f804,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_14
    | spl5_72 ),
    inference(subsumption_resolution,[],[f803,f144])).

fof(f144,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f803,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | spl5_72 ),
    inference(duplicate_literal_removal,[],[f802])).

fof(f802,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl5_72 ),
    inference(resolution,[],[f800,f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f800,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | spl5_72 ),
    inference(avatar_component_clause,[],[f798])).

fof(f801,plain,
    ( ~ spl5_72
    | spl5_16
    | ~ spl5_44
    | ~ spl5_46
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f791,f450,f417,f400,f155,f798])).

fof(f155,plain,
    ( spl5_16
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f400,plain,
    ( spl5_44
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f417,plain,
    ( spl5_46
  <=> sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f450,plain,
    ( spl5_50
  <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f791,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | spl5_16
    | ~ spl5_44
    | ~ spl5_46
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f157,f784])).

fof(f784,plain,
    ( sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl5_44
    | ~ spl5_46
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f783,f402])).

fof(f402,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f400])).

fof(f783,plain,
    ( sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl5_46
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f419,f452])).

fof(f452,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f450])).

fof(f419,plain,
    ( sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f417])).

fof(f157,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f780,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_29
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(avatar_contradiction_clause,[],[f779])).

fof(f779,plain,
    ( $false
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_29
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f778,f94])).

fof(f778,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_29
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f777,f99])).

fof(f99,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f777,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_6
    | ~ spl5_29
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f776,f104])).

fof(f776,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f775,f414])).

fof(f414,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl5_45
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f775,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f774,f599])).

fof(f599,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl5_58
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f774,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_52
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f773,f662])).

fof(f662,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl5_62
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f773,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_52
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f772,f462])).

fof(f462,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl5_52
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f772,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_63
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f771,f666])).

fof(f666,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl5_63
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f771,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | ~ spl5_64
    | spl5_69 ),
    inference(subsumption_resolution,[],[f769,f670])).

fof(f670,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl5_64
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f769,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29
    | spl5_69 ),
    inference(resolution,[],[f765,f262])).

fof(f262,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_29
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f765,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_69 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl5_69
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f766,plain,
    ( ~ spl5_69
    | ~ spl5_44
    | spl5_49
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f736,f450,f429,f400,f763])).

fof(f429,plain,
    ( spl5_49
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f736,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_44
    | spl5_49
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f735,f402])).

fof(f735,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_49
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f431,f452])).

fof(f431,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_49 ),
    inference(avatar_component_clause,[],[f429])).

fof(f734,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_67 ),
    inference(avatar_contradiction_clause,[],[f733])).

fof(f733,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_45
    | ~ spl5_52
    | ~ spl5_58
    | ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_67 ),
    inference(unit_resulting_resolution,[],[f79,f84,f89,f94,f99,f104,f109,f114,f124,f129,f414,f462,f599,f666,f662,f670,f728,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f728,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl5_67 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl5_67
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f129,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_11
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f124,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f114,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f109,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f729,plain,
    ( ~ spl5_67
    | ~ spl5_44
    | spl5_48
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f722,f450,f425,f400,f726])).

fof(f425,plain,
    ( spl5_48
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f722,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ spl5_44
    | spl5_48
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f721,f402])).

fof(f721,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl5_48
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f427,f452])).

fof(f427,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f425])).

fof(f718,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50
    | ~ spl5_57
    | spl5_64 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50
    | ~ spl5_57
    | spl5_64 ),
    inference(subsumption_resolution,[],[f716,f594])).

fof(f594,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl5_57
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f716,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50
    | spl5_64 ),
    inference(subsumption_resolution,[],[f549,f671])).

fof(f671,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl5_64 ),
    inference(avatar_component_clause,[],[f669])).

fof(f549,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f548,f79])).

fof(f548,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f547,f84])).

fof(f547,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f546,f89])).

fof(f546,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f545,f94])).

fof(f545,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f544,f99])).

fof(f544,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f543,f104])).

fof(f543,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f542,f129])).

fof(f542,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f541,f119])).

fof(f541,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f540,f139])).

fof(f540,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f532,f144])).

fof(f532,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_50 ),
    inference(superposition,[],[f66,f452])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f689,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44
    | ~ spl5_57
    | spl5_62 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44
    | ~ spl5_57
    | spl5_62 ),
    inference(subsumption_resolution,[],[f687,f594])).

fof(f687,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44
    | spl5_62 ),
    inference(subsumption_resolution,[],[f515,f663])).

fof(f663,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_62 ),
    inference(avatar_component_clause,[],[f661])).

fof(f515,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f514,f79])).

fof(f514,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f513,f84])).

fof(f513,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f512,f89])).

fof(f512,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f511,f94])).

fof(f511,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f510,f99])).

fof(f510,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f509,f104])).

fof(f509,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f508,f124])).

fof(f508,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f507,f119])).

fof(f507,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f506,f139])).

fof(f506,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f499,f144])).

fof(f499,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_44 ),
    inference(superposition,[],[f66,f402])).

fof(f673,plain,
    ( spl5_63
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50
    | ~ spl5_57 ),
    inference(avatar_split_clause,[],[f633,f593,f450,f142,f137,f127,f117,f102,f97,f92,f87,f82,f77,f665])).

fof(f633,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f559,f594])).

fof(f559,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f558,f79])).

fof(f558,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f557,f84])).

fof(f557,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f556,f89])).

fof(f556,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f555,f94])).

fof(f555,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f554,f99])).

fof(f554,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f553,f104])).

fof(f553,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f552,f129])).

fof(f552,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f551,f119])).

fof(f551,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f550,f139])).

fof(f550,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f533,f144])).

fof(f533,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_50 ),
    inference(superposition,[],[f65,f452])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f672,plain,
    ( ~ spl5_62
    | ~ spl5_63
    | ~ spl5_64
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f650,f597,f527,f460,f412,f289,f102,f97,f92,f669,f665,f661])).

fof(f289,plain,
    ( spl5_32
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f527,plain,
    ( spl5_55
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f650,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f565,f599])).

fof(f565,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55 ),
    inference(subsumption_resolution,[],[f564,f94])).

fof(f564,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55 ),
    inference(subsumption_resolution,[],[f563,f99])).

fof(f563,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_6
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55 ),
    inference(subsumption_resolution,[],[f562,f104])).

fof(f562,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_32
    | ~ spl5_45
    | ~ spl5_52
    | spl5_55 ),
    inference(subsumption_resolution,[],[f561,f414])).

fof(f561,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_32
    | ~ spl5_52
    | spl5_55 ),
    inference(subsumption_resolution,[],[f560,f462])).

fof(f560,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_32
    | spl5_55 ),
    inference(resolution,[],[f529,f290])).

fof(f290,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f289])).

fof(f529,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_55 ),
    inference(avatar_component_clause,[],[f527])).

fof(f609,plain,
    ( ~ spl5_3
    | spl5_57 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl5_3
    | spl5_57 ),
    inference(subsumption_resolution,[],[f606,f89])).

fof(f606,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_57 ),
    inference(resolution,[],[f595,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f595,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl5_57 ),
    inference(avatar_component_clause,[],[f593])).

fof(f600,plain,
    ( ~ spl5_57
    | spl5_58
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f525,f400,f142,f137,f122,f117,f102,f97,f92,f87,f82,f77,f597,f593])).

fof(f525,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f524,f79])).

fof(f524,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f523,f84])).

fof(f523,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f522,f89])).

fof(f522,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f521,f94])).

fof(f521,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f520,f99])).

fof(f520,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f519,f104])).

fof(f519,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f518,f124])).

fof(f518,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f517,f119])).

fof(f517,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f516,f139])).

fof(f516,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f500,f144])).

fof(f500,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_44 ),
    inference(superposition,[],[f65,f402])).

fof(f530,plain,
    ( ~ spl5_55
    | ~ spl5_44
    | spl5_51 ),
    inference(avatar_split_clause,[],[f497,f455,f400,f527])).

fof(f455,plain,
    ( spl5_51
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f497,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_44
    | spl5_51 ),
    inference(backward_demodulation,[],[f457,f402])).

fof(f457,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_51 ),
    inference(avatar_component_clause,[],[f455])).

fof(f463,plain,
    ( spl5_52
    | ~ spl5_11
    | ~ spl5_30
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f448,f378,f346,f265,f127,f460])).

fof(f265,plain,
    ( spl5_30
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f346,plain,
    ( spl5_37
  <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f378,plain,
    ( spl5_42
  <=> ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f448,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl5_11
    | ~ spl5_30
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f267,f391])).

fof(f391,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ spl5_11
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f388,f348])).

fof(f348,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f346])).

fof(f388,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl5_11
    | ~ spl5_42 ),
    inference(resolution,[],[f379,f129])).

fof(f379,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f378])).

fof(f267,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f265])).

fof(f458,plain,
    ( ~ spl5_51
    | ~ spl5_11
    | ~ spl5_37
    | ~ spl5_42
    | spl5_47 ),
    inference(avatar_split_clause,[],[f447,f421,f378,f346,f127,f455])).

fof(f421,plain,
    ( spl5_47
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f447,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_11
    | ~ spl5_37
    | ~ spl5_42
    | spl5_47 ),
    inference(backward_demodulation,[],[f423,f391])).

fof(f423,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_47 ),
    inference(avatar_component_clause,[],[f421])).

fof(f453,plain,
    ( spl5_50
    | ~ spl5_11
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f391,f378,f346,f127,f450])).

fof(f432,plain,
    ( spl5_46
    | ~ spl5_47
    | ~ spl5_48
    | ~ spl5_49
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f386,f374,f173,f142,f137,f102,f97,f92,f429,f425,f421,f417])).

fof(f173,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)
        | sK4 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f374,plain,
    ( spl5_41
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f386,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f385,f94])).

fof(f385,plain,
    ( v2_struct_0(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f384,f99])).

fof(f384,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f383,f104])).

fof(f383,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f382,f144])).

fof(f382,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_13
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f381,f139])).

fof(f381,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_19
    | ~ spl5_41 ),
    inference(resolution,[],[f375,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | sK4 = X0 )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f375,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f374])).

fof(f415,plain,
    ( spl5_45
    | ~ spl5_10
    | ~ spl5_28
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f398,f378,f333,f256,f122,f412])).

fof(f256,plain,
    ( spl5_28
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f333,plain,
    ( spl5_36
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f398,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ spl5_10
    | ~ spl5_28
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f258,f390])).

fof(f390,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f387,f335])).

fof(f335,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f333])).

fof(f387,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(resolution,[],[f379,f124])).

fof(f258,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f403,plain,
    ( spl5_44
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f390,f378,f333,f122,f400])).

fof(f380,plain,
    ( spl5_42
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f363,f351,f87,f82,f77,f378])).

fof(f351,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f363,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f362,f79])).

fof(f362,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f361,f84])).

fof(f361,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f360,f89])).

fof(f360,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_38 ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_38 ),
    inference(resolution,[],[f352,f57])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK0,X1)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f351])).

fof(f376,plain,
    ( spl5_41
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f344,f329,f132,f127,f122,f112,f107,f87,f82,f77,f374])).

fof(f132,plain,
    ( spl5_12
  <=> sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f329,plain,
    ( spl5_35
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f344,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f343,f79])).

fof(f343,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f342,f84])).

fof(f342,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f341,f89])).

fof(f341,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f340,f109])).

fof(f340,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f339,f124])).

fof(f339,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f338,f114])).

fof(f338,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f337,f129])).

fof(f337,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(superposition,[],[f330,f134])).

fof(f134,plain,
    ( sK0 = k1_tsep_1(sK0,sK2,sK3)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f330,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f329])).

fof(f353,plain,
    ( spl5_38
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f273,f252,f142,f137,f102,f97,f92,f351])).

fof(f252,plain,
    ( spl5_27
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f272,f94])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f271,f99])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f270,f104])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f269,f139])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK0,X1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_14
    | ~ spl5_27 ),
    inference(resolution,[],[f253,f144])).

fof(f253,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f252])).

fof(f349,plain,
    ( spl5_37
    | ~ spl5_11
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f325,f315,f127,f346])).

fof(f315,plain,
    ( spl5_34
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f325,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ spl5_11
    | ~ spl5_34 ),
    inference(resolution,[],[f316,f129])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f315])).

fof(f336,plain,
    ( spl5_36
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f324,f315,f122,f333])).

fof(f324,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(resolution,[],[f316,f124])).

fof(f331,plain,
    ( spl5_35
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f225,f117,f329])).

fof(f225,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
        | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
        | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4)))
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f60,f119])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f317,plain,
    ( spl5_34
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f246,f232,f142,f137,f102,f97,f92,f87,f82,f77,f315])).

fof(f232,plain,
    ( spl5_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f245,f79])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f244,f84])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f243,f89])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f242,f94])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f241,f99])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f240,f104])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f239,f139])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(resolution,[],[f233,f144])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f291,plain,
    ( spl5_32
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f220,f132,f127,f122,f112,f107,f87,f82,f77,f289])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f219,f79])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f218,f84])).

fof(f218,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f217,f89])).

fof(f217,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f216,f109])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f215,f124])).

fof(f215,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f214,f114])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f213,f129])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_12 ),
    inference(superposition,[],[f71,f134])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f32])).

fof(f268,plain,
    ( spl5_30
    | ~ spl5_11
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f248,f236,f127,f265])).

fof(f236,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f248,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ spl5_11
    | ~ spl5_26 ),
    inference(resolution,[],[f237,f129])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f263,plain,
    ( spl5_29
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f207,f132,f127,f122,f112,f107,f87,f82,f77,f261])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f206,f79])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f205,f84])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f204,f89])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_7
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f203,f109])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f202,f124])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_8
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f201,f114])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f200,f129])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_12 ),
    inference(superposition,[],[f70,f134])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f32])).

fof(f259,plain,
    ( spl5_28
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f247,f236,f122,f256])).

fof(f247,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(resolution,[],[f237,f124])).

fof(f254,plain,
    ( spl5_27
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f193,f117,f252])).

fof(f193,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4)
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl5_9 ),
    inference(resolution,[],[f59,f119])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f238,plain,
    ( spl5_26
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f230,f222,f87,f82,f77,f236])).

fof(f222,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f229,f79])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f228,f84])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f227,f89])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_24 ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_24 ),
    inference(resolution,[],[f223,f57])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK0,X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f234,plain,
    ( spl5_25
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f178,f117,f232])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl5_9 ),
    inference(resolution,[],[f61,f119])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f224,plain,
    ( spl5_24
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f212,f197,f142,f137,f102,f97,f92,f222])).

fof(f197,plain,
    ( spl5_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f211,f94])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f210,f99])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_6
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f209,f104])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f208,f139])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(resolution,[],[f198,f144])).

fof(f198,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl5_23
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f176,f117,f197])).

fof(f176,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f64,f119])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f175,plain,
    ( spl5_19
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f170,f166,f142,f137,f173])).

fof(f166,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(X0,X1,sK4,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | sK4 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)
        | sK4 = X0 )
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f169,f139])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
        | sK4 = X0 )
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(resolution,[],[f167,f144])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ r2_funct_2(X0,X1,sK4,X2)
        | ~ v1_funct_2(sK4,X0,X1)
        | sK4 = X2 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl5_18
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f164,f117,f166])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(X0,X1,sK4,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK4,X0,X1)
        | sK4 = X2 )
    | ~ spl5_9 ),
    inference(resolution,[],[f62,f119])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f158,plain,
    ( ~ spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f151,f132,f155])).

fof(f151,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f55,f134])).

fof(f55,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & sK0 = k1_tsep_1(sK0,sK2,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK0 = k1_tsep_1(sK0,X2,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK0 = k1_tsep_1(sK0,X2,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & sK0 = k1_tsep_1(sK0,X2,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & sK0 = k1_tsep_1(sK0,X2,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & sK0 = k1_tsep_1(sK0,sK2,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & sK0 = k1_tsep_1(sK0,sK2,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & sK0 = k1_tsep_1(sK0,sK2,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).

fof(f145,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f53,f137])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f51,f132])).

fof(f51,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f130,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f50,f127])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f125,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f120,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f52,f117])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f49,f112])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f47,f107])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f46,f102])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6294)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (6302)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (6285)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6282)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6284)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (6283)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (6292)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (6303)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (6281)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (6293)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (6295)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (6289)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (6288)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (6300)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (6304)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (6305)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (6298)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (6301)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (6297)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (6286)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (6296)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (6306)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (6299)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (6291)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.54  % (6290)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.55  % (6287)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.59  % (6283)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f820,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f158,f168,f175,f199,f224,f234,f238,f254,f259,f263,f268,f291,f317,f331,f336,f349,f353,f376,f380,f403,f415,f432,f453,f458,f463,f530,f600,f609,f672,f673,f689,f718,f729,f734,f766,f780,f801,f807,f814,f819])).
% 0.20/0.59  fof(f819,plain,(
% 0.20/0.59    ~spl5_6 | spl5_73),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f818])).
% 0.20/0.59  fof(f818,plain,(
% 0.20/0.59    $false | (~spl5_6 | spl5_73)),
% 0.20/0.59    inference(subsumption_resolution,[],[f816,f104])).
% 0.20/0.59  fof(f104,plain,(
% 0.20/0.59    l1_pre_topc(sK1) | ~spl5_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f102])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    spl5_6 <=> l1_pre_topc(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.59  fof(f816,plain,(
% 0.20/0.59    ~l1_pre_topc(sK1) | spl5_73),
% 0.20/0.59    inference(resolution,[],[f813,f56])).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.59  fof(f813,plain,(
% 0.20/0.59    ~l1_struct_0(sK1) | spl5_73),
% 0.20/0.59    inference(avatar_component_clause,[],[f811])).
% 0.20/0.59  fof(f811,plain,(
% 0.20/0.59    spl5_73 <=> l1_struct_0(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.20/0.59  fof(f814,plain,(
% 0.20/0.59    ~spl5_73 | spl5_4 | ~spl5_21),
% 0.20/0.59    inference(avatar_split_clause,[],[f809,f186,f92,f811])).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    spl5_4 <=> v2_struct_0(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.59  fof(f186,plain,(
% 0.20/0.59    spl5_21 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.59  fof(f809,plain,(
% 0.20/0.59    ~l1_struct_0(sK1) | (spl5_4 | ~spl5_21)),
% 0.20/0.59    inference(subsumption_resolution,[],[f808,f94])).
% 0.20/0.59  fof(f94,plain,(
% 0.20/0.59    ~v2_struct_0(sK1) | spl5_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f92])).
% 0.20/0.59  fof(f808,plain,(
% 0.20/0.59    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_21),
% 0.20/0.59    inference(resolution,[],[f188,f58])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.59    inference(flattening,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.59  fof(f188,plain,(
% 0.20/0.59    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_21),
% 0.20/0.59    inference(avatar_component_clause,[],[f186])).
% 0.20/0.59  fof(f807,plain,(
% 0.20/0.59    spl5_21 | ~spl5_9 | ~spl5_13 | ~spl5_14 | spl5_72),
% 0.20/0.59    inference(avatar_split_clause,[],[f806,f798,f142,f137,f117,f186])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    spl5_9 <=> v1_funct_1(sK4)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.59  fof(f137,plain,(
% 0.20/0.59    spl5_13 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.59  fof(f142,plain,(
% 0.20/0.59    spl5_14 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.59  fof(f798,plain,(
% 0.20/0.59    spl5_72 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 0.20/0.59  fof(f806,plain,(
% 0.20/0.59    v1_xboole_0(u1_struct_0(sK1)) | (~spl5_9 | ~spl5_13 | ~spl5_14 | spl5_72)),
% 0.20/0.59    inference(subsumption_resolution,[],[f805,f119])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    v1_funct_1(sK4) | ~spl5_9),
% 0.20/0.59    inference(avatar_component_clause,[],[f117])).
% 0.20/0.59  fof(f805,plain,(
% 0.20/0.59    ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | (~spl5_13 | ~spl5_14 | spl5_72)),
% 0.20/0.59    inference(subsumption_resolution,[],[f804,f139])).
% 0.20/0.59  fof(f139,plain,(
% 0.20/0.59    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_13),
% 0.20/0.59    inference(avatar_component_clause,[],[f137])).
% 0.20/0.59  fof(f804,plain,(
% 0.20/0.59    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | (~spl5_14 | spl5_72)),
% 0.20/0.59    inference(subsumption_resolution,[],[f803,f144])).
% 0.20/0.59  fof(f144,plain,(
% 0.20/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_14),
% 0.20/0.59    inference(avatar_component_clause,[],[f142])).
% 0.20/0.59  fof(f803,plain,(
% 0.20/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | v1_xboole_0(u1_struct_0(sK1)) | spl5_72),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f802])).
% 0.20/0.59  fof(f802,plain,(
% 0.20/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl5_72),
% 0.20/0.59    inference(resolution,[],[f800,f74])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f73])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.59    inference(nnf_transformation,[],[f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.59    inference(flattening,[],[f29])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.20/0.59  fof(f800,plain,(
% 0.20/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | spl5_72),
% 0.20/0.59    inference(avatar_component_clause,[],[f798])).
% 0.20/0.59  fof(f801,plain,(
% 0.20/0.59    ~spl5_72 | spl5_16 | ~spl5_44 | ~spl5_46 | ~spl5_50),
% 0.20/0.59    inference(avatar_split_clause,[],[f791,f450,f417,f400,f155,f798])).
% 0.20/0.59  fof(f155,plain,(
% 0.20/0.59    spl5_16 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.59  fof(f400,plain,(
% 0.20/0.59    spl5_44 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.20/0.59  fof(f417,plain,(
% 0.20/0.59    spl5_46 <=> sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.20/0.59  fof(f450,plain,(
% 0.20/0.59    spl5_50 <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.20/0.59  fof(f791,plain,(
% 0.20/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) | (spl5_16 | ~spl5_44 | ~spl5_46 | ~spl5_50)),
% 0.20/0.59    inference(backward_demodulation,[],[f157,f784])).
% 0.20/0.59  fof(f784,plain,(
% 0.20/0.59    sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) | (~spl5_44 | ~spl5_46 | ~spl5_50)),
% 0.20/0.59    inference(forward_demodulation,[],[f783,f402])).
% 0.20/0.59  fof(f402,plain,(
% 0.20/0.59    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~spl5_44),
% 0.20/0.59    inference(avatar_component_clause,[],[f400])).
% 0.20/0.59  fof(f783,plain,(
% 0.20/0.59    sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)) | (~spl5_46 | ~spl5_50)),
% 0.20/0.59    inference(forward_demodulation,[],[f419,f452])).
% 0.20/0.59  fof(f452,plain,(
% 0.20/0.59    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~spl5_50),
% 0.20/0.59    inference(avatar_component_clause,[],[f450])).
% 0.20/0.59  fof(f419,plain,(
% 0.20/0.59    sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~spl5_46),
% 0.20/0.59    inference(avatar_component_clause,[],[f417])).
% 0.20/0.59  fof(f157,plain,(
% 0.20/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | spl5_16),
% 0.20/0.59    inference(avatar_component_clause,[],[f155])).
% 0.20/0.59  fof(f780,plain,(
% 0.20/0.59    spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_29 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f779])).
% 0.20/0.59  fof(f779,plain,(
% 0.20/0.59    $false | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_29 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f778,f94])).
% 0.20/0.59  fof(f778,plain,(
% 0.20/0.59    v2_struct_0(sK1) | (~spl5_5 | ~spl5_6 | ~spl5_29 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f777,f99])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    v2_pre_topc(sK1) | ~spl5_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f97])).
% 0.20/0.59  fof(f97,plain,(
% 0.20/0.59    spl5_5 <=> v2_pre_topc(sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.59  fof(f777,plain,(
% 0.20/0.59    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_6 | ~spl5_29 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f776,f104])).
% 0.20/0.59  fof(f776,plain,(
% 0.20/0.59    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f775,f414])).
% 0.20/0.59  fof(f414,plain,(
% 0.20/0.59    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~spl5_45),
% 0.20/0.59    inference(avatar_component_clause,[],[f412])).
% 0.20/0.59  fof(f412,plain,(
% 0.20/0.59    spl5_45 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.20/0.59  fof(f775,plain,(
% 0.20/0.59    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f774,f599])).
% 0.20/0.59  fof(f599,plain,(
% 0.20/0.59    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl5_58),
% 0.20/0.59    inference(avatar_component_clause,[],[f597])).
% 0.20/0.59  fof(f597,plain,(
% 0.20/0.59    spl5_58 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.20/0.59  fof(f774,plain,(
% 0.20/0.59    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_52 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f773,f662])).
% 0.20/0.59  fof(f662,plain,(
% 0.20/0.59    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl5_62),
% 0.20/0.59    inference(avatar_component_clause,[],[f661])).
% 0.20/0.59  fof(f661,plain,(
% 0.20/0.59    spl5_62 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.20/0.59  fof(f773,plain,(
% 0.20/0.59    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_52 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 0.20/0.59    inference(subsumption_resolution,[],[f772,f462])).
% 0.20/0.59  fof(f462,plain,(
% 0.20/0.59    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~spl5_52),
% 0.20/0.59    inference(avatar_component_clause,[],[f460])).
% 0.20/0.59  fof(f460,plain,(
% 0.20/0.59    spl5_52 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.94/0.61  fof(f772,plain,(
% 1.94/0.61    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_63 | ~spl5_64 | spl5_69)),
% 1.94/0.61    inference(subsumption_resolution,[],[f771,f666])).
% 1.94/0.61  fof(f666,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl5_63),
% 1.94/0.61    inference(avatar_component_clause,[],[f665])).
% 1.94/0.61  fof(f665,plain,(
% 1.94/0.61    spl5_63 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 1.94/0.61  fof(f771,plain,(
% 1.94/0.61    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | ~spl5_64 | spl5_69)),
% 1.94/0.61    inference(subsumption_resolution,[],[f769,f670])).
% 1.94/0.61  fof(f670,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl5_64),
% 1.94/0.61    inference(avatar_component_clause,[],[f669])).
% 1.94/0.61  fof(f669,plain,(
% 1.94/0.61    spl5_64 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 1.94/0.61  fof(f769,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_29 | spl5_69)),
% 1.94/0.61    inference(resolution,[],[f765,f262])).
% 1.94/0.61  fof(f262,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_29),
% 1.94/0.61    inference(avatar_component_clause,[],[f261])).
% 1.94/0.61  fof(f261,plain,(
% 1.94/0.61    spl5_29 <=> ! [X1,X0,X2] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.94/0.61  fof(f765,plain,(
% 1.94/0.61    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | spl5_69),
% 1.94/0.61    inference(avatar_component_clause,[],[f763])).
% 1.94/0.61  fof(f763,plain,(
% 1.94/0.61    spl5_69 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 1.94/0.61  fof(f766,plain,(
% 1.94/0.61    ~spl5_69 | ~spl5_44 | spl5_49 | ~spl5_50),
% 1.94/0.61    inference(avatar_split_clause,[],[f736,f450,f429,f400,f763])).
% 1.94/0.61  fof(f429,plain,(
% 1.94/0.61    spl5_49 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.94/0.61  fof(f736,plain,(
% 1.94/0.61    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_44 | spl5_49 | ~spl5_50)),
% 1.94/0.61    inference(forward_demodulation,[],[f735,f402])).
% 1.94/0.61  fof(f735,plain,(
% 1.94/0.61    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) | (spl5_49 | ~spl5_50)),
% 1.94/0.61    inference(forward_demodulation,[],[f431,f452])).
% 1.94/0.61  fof(f431,plain,(
% 1.94/0.61    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | spl5_49),
% 1.94/0.61    inference(avatar_component_clause,[],[f429])).
% 1.94/0.61  fof(f734,plain,(
% 1.94/0.61    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_67),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f733])).
% 1.94/0.61  fof(f733,plain,(
% 1.94/0.61    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_45 | ~spl5_52 | ~spl5_58 | ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_67)),
% 1.94/0.61    inference(unit_resulting_resolution,[],[f79,f84,f89,f94,f99,f104,f109,f114,f124,f129,f414,f462,f599,f666,f662,f670,f728,f69])).
% 1.94/0.61  fof(f69,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f32])).
% 1.94/0.61  fof(f32,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f31])).
% 1.94/0.61  fof(f31,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f7])).
% 1.94/0.61  fof(f7,axiom,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.94/0.61  fof(f728,plain,(
% 1.94/0.61    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | spl5_67),
% 1.94/0.61    inference(avatar_component_clause,[],[f726])).
% 1.94/0.61  fof(f726,plain,(
% 1.94/0.61    spl5_67 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 1.94/0.61  fof(f129,plain,(
% 1.94/0.61    m1_pre_topc(sK3,sK0) | ~spl5_11),
% 1.94/0.61    inference(avatar_component_clause,[],[f127])).
% 1.94/0.61  fof(f127,plain,(
% 1.94/0.61    spl5_11 <=> m1_pre_topc(sK3,sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.94/0.61  fof(f124,plain,(
% 1.94/0.61    m1_pre_topc(sK2,sK0) | ~spl5_10),
% 1.94/0.61    inference(avatar_component_clause,[],[f122])).
% 1.94/0.61  fof(f122,plain,(
% 1.94/0.61    spl5_10 <=> m1_pre_topc(sK2,sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.94/0.61  fof(f114,plain,(
% 1.94/0.61    ~v2_struct_0(sK3) | spl5_8),
% 1.94/0.61    inference(avatar_component_clause,[],[f112])).
% 1.94/0.61  fof(f112,plain,(
% 1.94/0.61    spl5_8 <=> v2_struct_0(sK3)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.94/0.61  fof(f109,plain,(
% 1.94/0.61    ~v2_struct_0(sK2) | spl5_7),
% 1.94/0.61    inference(avatar_component_clause,[],[f107])).
% 1.94/0.61  fof(f107,plain,(
% 1.94/0.61    spl5_7 <=> v2_struct_0(sK2)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.94/0.61  fof(f89,plain,(
% 1.94/0.61    l1_pre_topc(sK0) | ~spl5_3),
% 1.94/0.61    inference(avatar_component_clause,[],[f87])).
% 1.94/0.61  fof(f87,plain,(
% 1.94/0.61    spl5_3 <=> l1_pre_topc(sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.94/0.61  fof(f84,plain,(
% 1.94/0.61    v2_pre_topc(sK0) | ~spl5_2),
% 1.94/0.61    inference(avatar_component_clause,[],[f82])).
% 1.94/0.61  fof(f82,plain,(
% 1.94/0.61    spl5_2 <=> v2_pre_topc(sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.94/0.61  fof(f79,plain,(
% 1.94/0.61    ~v2_struct_0(sK0) | spl5_1),
% 1.94/0.61    inference(avatar_component_clause,[],[f77])).
% 1.94/0.61  fof(f77,plain,(
% 1.94/0.61    spl5_1 <=> v2_struct_0(sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.94/0.61  fof(f729,plain,(
% 1.94/0.61    ~spl5_67 | ~spl5_44 | spl5_48 | ~spl5_50),
% 1.94/0.61    inference(avatar_split_clause,[],[f722,f450,f425,f400,f726])).
% 1.94/0.61  fof(f425,plain,(
% 1.94/0.61    spl5_48 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.94/0.61  fof(f722,plain,(
% 1.94/0.61    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | (~spl5_44 | spl5_48 | ~spl5_50)),
% 1.94/0.61    inference(forward_demodulation,[],[f721,f402])).
% 1.94/0.61  fof(f721,plain,(
% 1.94/0.61    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3))) | (spl5_48 | ~spl5_50)),
% 1.94/0.61    inference(forward_demodulation,[],[f427,f452])).
% 1.94/0.61  fof(f427,plain,(
% 1.94/0.61    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | spl5_48),
% 1.94/0.61    inference(avatar_component_clause,[],[f425])).
% 1.94/0.61  fof(f718,plain,(
% 1.94/0.61    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50 | ~spl5_57 | spl5_64),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f717])).
% 1.94/0.61  fof(f717,plain,(
% 1.94/0.61    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50 | ~spl5_57 | spl5_64)),
% 1.94/0.61    inference(subsumption_resolution,[],[f716,f594])).
% 1.94/0.61  fof(f594,plain,(
% 1.94/0.61    m1_pre_topc(sK0,sK0) | ~spl5_57),
% 1.94/0.61    inference(avatar_component_clause,[],[f593])).
% 1.94/0.61  fof(f593,plain,(
% 1.94/0.61    spl5_57 <=> m1_pre_topc(sK0,sK0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 1.94/0.61  fof(f716,plain,(
% 1.94/0.61    ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50 | spl5_64)),
% 1.94/0.61    inference(subsumption_resolution,[],[f549,f671])).
% 1.94/0.61  fof(f671,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl5_64),
% 1.94/0.61    inference(avatar_component_clause,[],[f669])).
% 1.94/0.61  fof(f549,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f548,f79])).
% 1.94/0.61  fof(f548,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f547,f84])).
% 1.94/0.61  fof(f547,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f546,f89])).
% 1.94/0.61  fof(f546,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f545,f94])).
% 1.94/0.61  fof(f545,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f544,f99])).
% 1.94/0.61  fof(f544,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f543,f104])).
% 1.94/0.61  fof(f543,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f542,f129])).
% 1.94/0.61  fof(f542,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f541,f119])).
% 1.94/0.61  fof(f541,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f540,f139])).
% 1.94/0.61  fof(f540,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f532,f144])).
% 1.94/0.61  fof(f532,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_50),
% 1.94/0.61    inference(superposition,[],[f66,f452])).
% 1.94/0.61  fof(f66,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f28,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f27])).
% 1.94/0.61  fof(f27,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f8])).
% 1.94/0.61  fof(f8,axiom,(
% 1.94/0.61    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.94/0.61  fof(f689,plain,(
% 1.94/0.61    spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44 | ~spl5_57 | spl5_62),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f688])).
% 1.94/0.61  fof(f688,plain,(
% 1.94/0.61    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44 | ~spl5_57 | spl5_62)),
% 1.94/0.61    inference(subsumption_resolution,[],[f687,f594])).
% 1.94/0.61  fof(f687,plain,(
% 1.94/0.61    ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44 | spl5_62)),
% 1.94/0.61    inference(subsumption_resolution,[],[f515,f663])).
% 1.94/0.61  fof(f663,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_62),
% 1.94/0.61    inference(avatar_component_clause,[],[f661])).
% 1.94/0.61  fof(f515,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f514,f79])).
% 1.94/0.61  fof(f514,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f513,f84])).
% 1.94/0.61  fof(f513,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f512,f89])).
% 1.94/0.61  fof(f512,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f511,f94])).
% 1.94/0.61  fof(f511,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f510,f99])).
% 1.94/0.61  fof(f510,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f509,f104])).
% 1.94/0.61  fof(f509,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f508,f124])).
% 1.94/0.61  fof(f508,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f507,f119])).
% 1.94/0.61  fof(f507,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f506,f139])).
% 1.94/0.61  fof(f506,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f499,f144])).
% 1.94/0.61  fof(f499,plain,(
% 1.94/0.61    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_44),
% 1.94/0.61    inference(superposition,[],[f66,f402])).
% 1.94/0.61  fof(f673,plain,(
% 1.94/0.61    spl5_63 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50 | ~spl5_57),
% 1.94/0.61    inference(avatar_split_clause,[],[f633,f593,f450,f142,f137,f127,f117,f102,f97,f92,f87,f82,f77,f665])).
% 1.94/0.61  fof(f633,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50 | ~spl5_57)),
% 1.94/0.61    inference(subsumption_resolution,[],[f559,f594])).
% 1.94/0.61  fof(f559,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f558,f79])).
% 1.94/0.61  fof(f558,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f557,f84])).
% 1.94/0.61  fof(f557,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f556,f89])).
% 1.94/0.61  fof(f556,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f555,f94])).
% 1.94/0.61  fof(f555,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f554,f99])).
% 1.94/0.61  fof(f554,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f553,f104])).
% 1.94/0.61  fof(f553,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_11 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f552,f129])).
% 1.94/0.61  fof(f552,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f551,f119])).
% 1.94/0.61  fof(f551,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_13 | ~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f550,f139])).
% 1.94/0.61  fof(f550,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_14 | ~spl5_50)),
% 1.94/0.61    inference(subsumption_resolution,[],[f533,f144])).
% 1.94/0.61  fof(f533,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_50),
% 1.94/0.61    inference(superposition,[],[f65,f452])).
% 1.94/0.61  fof(f65,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f672,plain,(
% 1.94/0.61    ~spl5_62 | ~spl5_63 | ~spl5_64 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55 | ~spl5_58),
% 1.94/0.61    inference(avatar_split_clause,[],[f650,f597,f527,f460,f412,f289,f102,f97,f92,f669,f665,f661])).
% 1.94/0.61  fof(f289,plain,(
% 1.94/0.61    spl5_32 <=> ! [X1,X0,X2] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.94/0.61  fof(f527,plain,(
% 1.94/0.61    spl5_55 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.94/0.61  fof(f650,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55 | ~spl5_58)),
% 1.94/0.61    inference(subsumption_resolution,[],[f565,f599])).
% 1.94/0.61  fof(f565,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55)),
% 1.94/0.61    inference(subsumption_resolution,[],[f564,f94])).
% 1.94/0.61  fof(f564,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl5_5 | ~spl5_6 | ~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55)),
% 1.94/0.61    inference(subsumption_resolution,[],[f563,f99])).
% 1.94/0.61  fof(f563,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_6 | ~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55)),
% 1.94/0.61    inference(subsumption_resolution,[],[f562,f104])).
% 1.94/0.61  fof(f562,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_32 | ~spl5_45 | ~spl5_52 | spl5_55)),
% 1.94/0.61    inference(subsumption_resolution,[],[f561,f414])).
% 1.94/0.61  fof(f561,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_32 | ~spl5_52 | spl5_55)),
% 1.94/0.61    inference(subsumption_resolution,[],[f560,f462])).
% 1.94/0.61  fof(f560,plain,(
% 1.94/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_32 | spl5_55)),
% 1.94/0.61    inference(resolution,[],[f529,f290])).
% 1.94/0.61  fof(f290,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_32),
% 1.94/0.61    inference(avatar_component_clause,[],[f289])).
% 1.94/0.61  fof(f529,plain,(
% 1.94/0.61    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_55),
% 1.94/0.61    inference(avatar_component_clause,[],[f527])).
% 1.94/0.61  fof(f609,plain,(
% 1.94/0.61    ~spl5_3 | spl5_57),
% 1.94/0.61    inference(avatar_contradiction_clause,[],[f608])).
% 1.94/0.61  fof(f608,plain,(
% 1.94/0.61    $false | (~spl5_3 | spl5_57)),
% 1.94/0.61    inference(subsumption_resolution,[],[f606,f89])).
% 1.94/0.61  fof(f606,plain,(
% 1.94/0.61    ~l1_pre_topc(sK0) | spl5_57),
% 1.94/0.61    inference(resolution,[],[f595,f57])).
% 1.94/0.61  fof(f57,plain,(
% 1.94/0.61    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f16])).
% 1.94/0.61  fof(f16,plain,(
% 1.94/0.61    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.94/0.61    inference(ennf_transformation,[],[f10])).
% 1.94/0.61  fof(f10,axiom,(
% 1.94/0.61    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.94/0.61  fof(f595,plain,(
% 1.94/0.61    ~m1_pre_topc(sK0,sK0) | spl5_57),
% 1.94/0.61    inference(avatar_component_clause,[],[f593])).
% 1.94/0.61  fof(f600,plain,(
% 1.94/0.61    ~spl5_57 | spl5_58 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44),
% 1.94/0.61    inference(avatar_split_clause,[],[f525,f400,f142,f137,f122,f117,f102,f97,f92,f87,f82,f77,f597,f593])).
% 1.94/0.61  fof(f525,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f524,f79])).
% 1.94/0.61  fof(f524,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f523,f84])).
% 1.94/0.61  fof(f523,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f522,f89])).
% 1.94/0.61  fof(f522,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f521,f94])).
% 1.94/0.61  fof(f521,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f520,f99])).
% 1.94/0.61  fof(f520,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f519,f104])).
% 1.94/0.61  fof(f519,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_10 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f518,f124])).
% 1.94/0.61  fof(f518,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_9 | ~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f517,f119])).
% 1.94/0.61  fof(f517,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_13 | ~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f516,f139])).
% 1.94/0.61  fof(f516,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_14 | ~spl5_44)),
% 1.94/0.61    inference(subsumption_resolution,[],[f500,f144])).
% 1.94/0.61  fof(f500,plain,(
% 1.94/0.61    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_44),
% 1.94/0.61    inference(superposition,[],[f65,f402])).
% 1.94/0.61  fof(f530,plain,(
% 1.94/0.61    ~spl5_55 | ~spl5_44 | spl5_51),
% 1.94/0.61    inference(avatar_split_clause,[],[f497,f455,f400,f527])).
% 1.94/0.61  fof(f455,plain,(
% 1.94/0.61    spl5_51 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.94/0.61  fof(f497,plain,(
% 1.94/0.61    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl5_44 | spl5_51)),
% 1.94/0.61    inference(backward_demodulation,[],[f457,f402])).
% 1.94/0.61  fof(f457,plain,(
% 1.94/0.61    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_51),
% 1.94/0.61    inference(avatar_component_clause,[],[f455])).
% 1.94/0.61  fof(f463,plain,(
% 1.94/0.61    spl5_52 | ~spl5_11 | ~spl5_30 | ~spl5_37 | ~spl5_42),
% 1.94/0.61    inference(avatar_split_clause,[],[f448,f378,f346,f265,f127,f460])).
% 1.94/0.61  fof(f265,plain,(
% 1.94/0.61    spl5_30 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.94/0.61  fof(f346,plain,(
% 1.94/0.61    spl5_37 <=> k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.94/0.61  fof(f378,plain,(
% 1.94/0.61    spl5_42 <=> ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.94/0.61  fof(f448,plain,(
% 1.94/0.61    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | (~spl5_11 | ~spl5_30 | ~spl5_37 | ~spl5_42)),
% 1.94/0.61    inference(backward_demodulation,[],[f267,f391])).
% 1.94/0.61  fof(f391,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | (~spl5_11 | ~spl5_37 | ~spl5_42)),
% 1.94/0.61    inference(forward_demodulation,[],[f388,f348])).
% 1.94/0.61  fof(f348,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~spl5_37),
% 1.94/0.61    inference(avatar_component_clause,[],[f346])).
% 1.94/0.61  fof(f388,plain,(
% 1.94/0.61    k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | (~spl5_11 | ~spl5_42)),
% 1.94/0.61    inference(resolution,[],[f379,f129])).
% 1.94/0.61  fof(f379,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl5_42),
% 1.94/0.61    inference(avatar_component_clause,[],[f378])).
% 1.94/0.61  fof(f267,plain,(
% 1.94/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~spl5_30),
% 1.94/0.61    inference(avatar_component_clause,[],[f265])).
% 1.94/0.61  fof(f458,plain,(
% 1.94/0.61    ~spl5_51 | ~spl5_11 | ~spl5_37 | ~spl5_42 | spl5_47),
% 1.94/0.61    inference(avatar_split_clause,[],[f447,f421,f378,f346,f127,f455])).
% 1.94/0.61  fof(f421,plain,(
% 1.94/0.61    spl5_47 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.94/0.61  fof(f447,plain,(
% 1.94/0.61    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl5_11 | ~spl5_37 | ~spl5_42 | spl5_47)),
% 1.94/0.61    inference(backward_demodulation,[],[f423,f391])).
% 1.94/0.61  fof(f423,plain,(
% 1.94/0.61    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_47),
% 1.94/0.61    inference(avatar_component_clause,[],[f421])).
% 1.94/0.61  fof(f453,plain,(
% 1.94/0.61    spl5_50 | ~spl5_11 | ~spl5_37 | ~spl5_42),
% 1.94/0.61    inference(avatar_split_clause,[],[f391,f378,f346,f127,f450])).
% 1.94/0.61  fof(f432,plain,(
% 1.94/0.61    spl5_46 | ~spl5_47 | ~spl5_48 | ~spl5_49 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_19 | ~spl5_41),
% 1.94/0.61    inference(avatar_split_clause,[],[f386,f374,f173,f142,f137,f102,f97,f92,f429,f425,f421,f417])).
% 1.94/0.61  fof(f173,plain,(
% 1.94/0.61    spl5_19 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) | sK4 = X0)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.94/0.61  fof(f374,plain,(
% 1.94/0.61    spl5_41 <=> ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.94/0.61  fof(f386,plain,(
% 1.94/0.61    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(subsumption_resolution,[],[f385,f94])).
% 1.94/0.61  fof(f385,plain,(
% 1.94/0.61    v2_struct_0(sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(subsumption_resolution,[],[f384,f99])).
% 1.94/0.61  fof(f384,plain,(
% 1.94/0.61    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(subsumption_resolution,[],[f383,f104])).
% 1.94/0.61  fof(f383,plain,(
% 1.94/0.61    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_13 | ~spl5_14 | ~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(subsumption_resolution,[],[f382,f144])).
% 1.94/0.61  fof(f382,plain,(
% 1.94/0.61    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_13 | ~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(subsumption_resolution,[],[f381,f139])).
% 1.94/0.61  fof(f381,plain,(
% 1.94/0.61    ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_19 | ~spl5_41)),
% 1.94/0.61    inference(resolution,[],[f375,f174])).
% 1.94/0.61  fof(f174,plain,(
% 1.94/0.61    ( ! [X0] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = X0) ) | ~spl5_19),
% 1.94/0.61    inference(avatar_component_clause,[],[f173])).
% 1.94/0.61  fof(f375,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_41),
% 1.94/0.61    inference(avatar_component_clause,[],[f374])).
% 1.94/0.61  fof(f415,plain,(
% 1.94/0.61    spl5_45 | ~spl5_10 | ~spl5_28 | ~spl5_36 | ~spl5_42),
% 1.94/0.61    inference(avatar_split_clause,[],[f398,f378,f333,f256,f122,f412])).
% 1.94/0.61  fof(f256,plain,(
% 1.94/0.61    spl5_28 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.94/0.61  fof(f333,plain,(
% 1.94/0.61    spl5_36 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 1.94/0.61  fof(f398,plain,(
% 1.94/0.61    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | (~spl5_10 | ~spl5_28 | ~spl5_36 | ~spl5_42)),
% 1.94/0.61    inference(backward_demodulation,[],[f258,f390])).
% 1.94/0.61  fof(f390,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | (~spl5_10 | ~spl5_36 | ~spl5_42)),
% 1.94/0.61    inference(forward_demodulation,[],[f387,f335])).
% 1.94/0.61  fof(f335,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl5_36),
% 1.94/0.61    inference(avatar_component_clause,[],[f333])).
% 1.94/0.61  fof(f387,plain,(
% 1.94/0.61    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl5_10 | ~spl5_42)),
% 1.94/0.61    inference(resolution,[],[f379,f124])).
% 1.94/0.61  fof(f258,plain,(
% 1.94/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~spl5_28),
% 1.94/0.61    inference(avatar_component_clause,[],[f256])).
% 1.94/0.61  fof(f403,plain,(
% 1.94/0.61    spl5_44 | ~spl5_10 | ~spl5_36 | ~spl5_42),
% 1.94/0.61    inference(avatar_split_clause,[],[f390,f378,f333,f122,f400])).
% 1.94/0.61  fof(f380,plain,(
% 1.94/0.61    spl5_42 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_38),
% 1.94/0.61    inference(avatar_split_clause,[],[f363,f351,f87,f82,f77,f378])).
% 1.94/0.61  fof(f351,plain,(
% 1.94/0.61    spl5_38 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.94/0.61  fof(f363,plain,(
% 1.94/0.61    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_38)),
% 1.94/0.61    inference(subsumption_resolution,[],[f362,f79])).
% 1.94/0.61  fof(f362,plain,(
% 1.94/0.61    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38)),
% 1.94/0.61    inference(subsumption_resolution,[],[f361,f84])).
% 1.94/0.61  fof(f361,plain,(
% 1.94/0.61    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_38)),
% 1.94/0.61    inference(subsumption_resolution,[],[f360,f89])).
% 1.94/0.61  fof(f360,plain,(
% 1.94/0.61    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_38),
% 1.94/0.61    inference(duplicate_literal_removal,[],[f359])).
% 1.94/0.61  fof(f359,plain,(
% 1.94/0.61    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK0,X0,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)) ) | ~spl5_38),
% 1.94/0.61    inference(resolution,[],[f352,f57])).
% 1.94/0.61  fof(f352,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(sK0,X1) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_38),
% 1.94/0.61    inference(avatar_component_clause,[],[f351])).
% 1.94/0.61  fof(f376,plain,(
% 1.94/0.61    spl5_41 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35),
% 1.94/0.61    inference(avatar_split_clause,[],[f344,f329,f132,f127,f122,f112,f107,f87,f82,f77,f374])).
% 1.94/0.61  fof(f132,plain,(
% 1.94/0.61    spl5_12 <=> sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.94/0.61  fof(f329,plain,(
% 1.94/0.61    spl5_35 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.94/0.61  fof(f344,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f343,f79])).
% 1.94/0.61  fof(f343,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f342,f84])).
% 1.94/0.61  fof(f342,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f341,f89])).
% 1.94/0.61  fof(f341,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f340,f109])).
% 1.94/0.61  fof(f340,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f339,f124])).
% 1.94/0.61  fof(f339,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f338,f114])).
% 1.94/0.61  fof(f338,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_11 | ~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(subsumption_resolution,[],[f337,f129])).
% 1.94/0.61  fof(f337,plain,(
% 1.94/0.61    ( ! [X0] : (r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0),sK4,k10_tmap_1(sK0,X0,sK2,sK3,k3_tmap_1(sK0,X0,sK0,sK2,sK4),k3_tmap_1(sK0,X0,sK0,sK3,sK4))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_12 | ~spl5_35)),
% 1.94/0.61    inference(superposition,[],[f330,f134])).
% 1.94/0.61  fof(f134,plain,(
% 1.94/0.61    sK0 = k1_tsep_1(sK0,sK2,sK3) | ~spl5_12),
% 1.94/0.61    inference(avatar_component_clause,[],[f132])).
% 1.94/0.61  fof(f330,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_35),
% 1.94/0.61    inference(avatar_component_clause,[],[f329])).
% 1.94/0.61  fof(f353,plain,(
% 1.94/0.61    spl5_38 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_27),
% 1.94/0.61    inference(avatar_split_clause,[],[f273,f252,f142,f137,f102,f97,f92,f351])).
% 1.94/0.61  fof(f252,plain,(
% 1.94/0.61    spl5_27 <=> ! [X1,X3,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.94/0.61  fof(f273,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_27)),
% 1.94/0.61    inference(subsumption_resolution,[],[f272,f94])).
% 1.94/0.61  fof(f272,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_27)),
% 1.94/0.61    inference(subsumption_resolution,[],[f271,f99])).
% 1.94/0.61  fof(f271,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_27)),
% 1.94/0.61    inference(subsumption_resolution,[],[f270,f104])).
% 1.94/0.61  fof(f270,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl5_13 | ~spl5_14 | ~spl5_27)),
% 1.94/0.61    inference(subsumption_resolution,[],[f269,f139])).
% 1.94/0.61  fof(f269,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK0,X0,sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl5_14 | ~spl5_27)),
% 1.94/0.61    inference(resolution,[],[f253,f144])).
% 1.94/0.61  fof(f253,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_27),
% 1.94/0.61    inference(avatar_component_clause,[],[f252])).
% 1.94/0.61  fof(f349,plain,(
% 1.94/0.61    spl5_37 | ~spl5_11 | ~spl5_34),
% 1.94/0.61    inference(avatar_split_clause,[],[f325,f315,f127,f346])).
% 1.94/0.61  fof(f315,plain,(
% 1.94/0.61    spl5_34 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.94/0.61  fof(f325,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | (~spl5_11 | ~spl5_34)),
% 1.94/0.61    inference(resolution,[],[f316,f129])).
% 1.94/0.61  fof(f316,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl5_34),
% 1.94/0.61    inference(avatar_component_clause,[],[f315])).
% 1.94/0.61  fof(f336,plain,(
% 1.94/0.61    spl5_36 | ~spl5_10 | ~spl5_34),
% 1.94/0.61    inference(avatar_split_clause,[],[f324,f315,f122,f333])).
% 1.94/0.61  fof(f324,plain,(
% 1.94/0.61    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | (~spl5_10 | ~spl5_34)),
% 1.94/0.61    inference(resolution,[],[f316,f124])).
% 1.94/0.61  fof(f331,plain,(
% 1.94/0.61    spl5_35 | ~spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f225,f117,f329])).
% 1.94/0.61  fof(f225,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),sK4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,sK4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,sK4))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_9),
% 1.94/0.61    inference(resolution,[],[f60,f119])).
% 1.94/0.61  fof(f60,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f22])).
% 1.94/0.61  fof(f22,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f21])).
% 1.94/0.61  fof(f21,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f9])).
% 1.94/0.61  fof(f9,axiom,(
% 1.94/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).
% 1.94/0.61  fof(f317,plain,(
% 1.94/0.61    spl5_34 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25),
% 1.94/0.61    inference(avatar_split_clause,[],[f246,f232,f142,f137,f102,f97,f92,f87,f82,f77,f315])).
% 1.94/0.61  fof(f232,plain,(
% 1.94/0.61    spl5_25 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.94/0.61  fof(f246,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f245,f79])).
% 1.94/0.61  fof(f245,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f244,f84])).
% 1.94/0.61  fof(f244,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f243,f89])).
% 1.94/0.61  fof(f243,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f242,f94])).
% 1.94/0.61  fof(f242,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f241,f99])).
% 1.94/0.61  fof(f241,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f240,f104])).
% 1.94/0.61  fof(f240,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_13 | ~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(subsumption_resolution,[],[f239,f139])).
% 1.94/0.61  fof(f239,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_tmap_1(sK0,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_14 | ~spl5_25)),
% 1.94/0.61    inference(resolution,[],[f233,f144])).
% 1.94/0.61  fof(f233,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_25),
% 1.94/0.61    inference(avatar_component_clause,[],[f232])).
% 1.94/0.61  fof(f291,plain,(
% 1.94/0.61    spl5_32 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 1.94/0.61    inference(avatar_split_clause,[],[f220,f132,f127,f122,f112,f107,f87,f82,f77,f289])).
% 1.94/0.61  fof(f220,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f219,f79])).
% 1.94/0.61  fof(f219,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f218,f84])).
% 1.94/0.61  fof(f218,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f217,f89])).
% 1.94/0.61  fof(f217,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f216,f109])).
% 1.94/0.61  fof(f216,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f215,f124])).
% 1.94/0.61  fof(f215,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f214,f114])).
% 1.94/0.61  fof(f214,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f213,f129])).
% 1.94/0.61  fof(f213,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_12),
% 1.94/0.61    inference(superposition,[],[f71,f134])).
% 1.94/0.61  fof(f71,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f32])).
% 1.94/0.61  fof(f268,plain,(
% 1.94/0.61    spl5_30 | ~spl5_11 | ~spl5_26),
% 1.94/0.61    inference(avatar_split_clause,[],[f248,f236,f127,f265])).
% 1.94/0.61  fof(f236,plain,(
% 1.94/0.61    spl5_26 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.94/0.61  fof(f248,plain,(
% 1.94/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | (~spl5_11 | ~spl5_26)),
% 1.94/0.61    inference(resolution,[],[f237,f129])).
% 1.94/0.61  fof(f237,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))) ) | ~spl5_26),
% 1.94/0.61    inference(avatar_component_clause,[],[f236])).
% 1.94/0.61  fof(f263,plain,(
% 1.94/0.61    spl5_29 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 1.94/0.61    inference(avatar_split_clause,[],[f207,f132,f127,f122,f112,f107,f87,f82,f77,f261])).
% 1.94/0.61  fof(f207,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f206,f79])).
% 1.94/0.61  fof(f206,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f205,f84])).
% 1.94/0.61  fof(f205,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f204,f89])).
% 1.94/0.61  fof(f204,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_7 | spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f203,f109])).
% 1.94/0.61  fof(f203,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f202,f124])).
% 1.94/0.61  fof(f202,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_8 | ~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f201,f114])).
% 1.94/0.61  fof(f201,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_11 | ~spl5_12)),
% 1.94/0.61    inference(subsumption_resolution,[],[f200,f129])).
% 1.94/0.61  fof(f200,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_12),
% 1.94/0.61    inference(superposition,[],[f70,f134])).
% 1.94/0.61  fof(f70,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f32])).
% 1.94/0.61  fof(f259,plain,(
% 1.94/0.61    spl5_28 | ~spl5_10 | ~spl5_26),
% 1.94/0.61    inference(avatar_split_clause,[],[f247,f236,f122,f256])).
% 1.94/0.61  fof(f247,plain,(
% 1.94/0.61    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | (~spl5_10 | ~spl5_26)),
% 1.94/0.61    inference(resolution,[],[f237,f124])).
% 1.94/0.61  fof(f254,plain,(
% 1.94/0.61    spl5_27 | ~spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f193,f117,f252])).
% 1.94/0.61  fof(f193,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k3_tmap_1(X3,X2,X1,X0,sK4) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl5_9),
% 1.94/0.61    inference(resolution,[],[f59,f119])).
% 1.94/0.61  fof(f59,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f20])).
% 1.94/0.61  fof(f20,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f19])).
% 1.94/0.61  fof(f19,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f6])).
% 1.94/0.61  fof(f6,axiom,(
% 1.94/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.94/0.61  fof(f238,plain,(
% 1.94/0.61    spl5_26 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_24),
% 1.94/0.61    inference(avatar_split_clause,[],[f230,f222,f87,f82,f77,f236])).
% 1.94/0.61  fof(f222,plain,(
% 1.94/0.61    spl5_24 <=> ! [X1,X0] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.94/0.61  fof(f230,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_24)),
% 1.94/0.61    inference(subsumption_resolution,[],[f229,f79])).
% 1.94/0.61  fof(f229,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_24)),
% 1.94/0.61    inference(subsumption_resolution,[],[f228,f84])).
% 1.94/0.61  fof(f228,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_24)),
% 1.94/0.61    inference(subsumption_resolution,[],[f227,f89])).
% 1.94/0.61  fof(f227,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_24),
% 1.94/0.61    inference(duplicate_literal_removal,[],[f226])).
% 1.94/0.61  fof(f226,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,X0,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)) ) | ~spl5_24),
% 1.94/0.61    inference(resolution,[],[f223,f57])).
% 1.94/0.61  fof(f223,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~m1_pre_topc(sK0,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_24),
% 1.94/0.61    inference(avatar_component_clause,[],[f222])).
% 1.94/0.61  fof(f234,plain,(
% 1.94/0.61    spl5_25 | ~spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f178,f117,f232])).
% 1.94/0.61  fof(f178,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k2_tmap_1(X1,X2,sK4,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl5_9),
% 1.94/0.61    inference(resolution,[],[f61,f119])).
% 1.94/0.61  fof(f61,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f24])).
% 1.94/0.61  fof(f24,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f23])).
% 1.94/0.61  fof(f23,plain,(
% 1.94/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f5])).
% 1.94/0.61  fof(f5,axiom,(
% 1.94/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.94/0.61  fof(f224,plain,(
% 1.94/0.61    spl5_24 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_23),
% 1.94/0.61    inference(avatar_split_clause,[],[f212,f197,f142,f137,f102,f97,f92,f222])).
% 1.94/0.61  fof(f197,plain,(
% 1.94/0.61    spl5_23 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.94/0.61  fof(f212,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_23)),
% 1.94/0.61    inference(subsumption_resolution,[],[f211,f94])).
% 1.94/0.61  fof(f211,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_5 | ~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_23)),
% 1.94/0.61    inference(subsumption_resolution,[],[f210,f99])).
% 1.94/0.61  fof(f210,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_6 | ~spl5_13 | ~spl5_14 | ~spl5_23)),
% 1.94/0.61    inference(subsumption_resolution,[],[f209,f104])).
% 1.94/0.61  fof(f209,plain,(
% 1.94/0.61    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_13 | ~spl5_14 | ~spl5_23)),
% 1.94/0.61    inference(subsumption_resolution,[],[f208,f139])).
% 1.94/0.61  fof(f208,plain,(
% 1.94/0.61    ( ! [X0,X1] : (~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_14 | ~spl5_23)),
% 1.94/0.61    inference(resolution,[],[f198,f144])).
% 1.94/0.61  fof(f198,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_23),
% 1.94/0.61    inference(avatar_component_clause,[],[f197])).
% 1.94/0.61  fof(f199,plain,(
% 1.94/0.61    spl5_23 | ~spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f176,f117,f197])).
% 1.94/0.61  fof(f176,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK4)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl5_9),
% 1.94/0.61    inference(resolution,[],[f64,f119])).
% 1.94/0.61  fof(f64,plain,(
% 1.94/0.61    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/0.61    inference(cnf_transformation,[],[f28])).
% 1.94/0.61  fof(f175,plain,(
% 1.94/0.61    spl5_19 | ~spl5_13 | ~spl5_14 | ~spl5_18),
% 1.94/0.61    inference(avatar_split_clause,[],[f170,f166,f142,f137,f173])).
% 1.94/0.61  fof(f166,plain,(
% 1.94/0.61    spl5_18 <=> ! [X1,X0,X2] : (~r2_funct_2(X0,X1,sK4,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | sK4 = X2)),
% 1.94/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.94/0.61  fof(f170,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) | sK4 = X0) ) | (~spl5_13 | ~spl5_14 | ~spl5_18)),
% 1.94/0.61    inference(subsumption_resolution,[],[f169,f139])).
% 1.94/0.61  fof(f169,plain,(
% 1.94/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | sK4 = X0) ) | (~spl5_14 | ~spl5_18)),
% 1.94/0.61    inference(resolution,[],[f167,f144])).
% 1.94/0.61  fof(f167,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~r2_funct_2(X0,X1,sK4,X2) | ~v1_funct_2(sK4,X0,X1) | sK4 = X2) ) | ~spl5_18),
% 1.94/0.61    inference(avatar_component_clause,[],[f166])).
% 1.94/0.61  fof(f168,plain,(
% 1.94/0.61    spl5_18 | ~spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f164,f117,f166])).
% 1.94/0.61  fof(f164,plain,(
% 1.94/0.61    ( ! [X2,X0,X1] : (~r2_funct_2(X0,X1,sK4,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK4,X0,X1) | sK4 = X2) ) | ~spl5_9),
% 1.94/0.61    inference(resolution,[],[f62,f119])).
% 1.94/0.61  fof(f62,plain,(
% 1.94/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | X2 = X3) )),
% 1.94/0.61    inference(cnf_transformation,[],[f39])).
% 1.94/0.61  fof(f39,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.94/0.61    inference(nnf_transformation,[],[f26])).
% 1.94/0.61  fof(f26,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.94/0.61    inference(flattening,[],[f25])).
% 1.94/0.61  fof(f25,plain,(
% 1.94/0.61    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.94/0.61    inference(ennf_transformation,[],[f1])).
% 1.94/0.61  fof(f1,axiom,(
% 1.94/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.94/0.61  fof(f158,plain,(
% 1.94/0.61    ~spl5_16 | ~spl5_12),
% 1.94/0.61    inference(avatar_split_clause,[],[f151,f132,f155])).
% 1.94/0.61  fof(f151,plain,(
% 1.94/0.61    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) | ~spl5_12),
% 1.94/0.61    inference(forward_demodulation,[],[f55,f134])).
% 1.94/0.61  fof(f55,plain,(
% 1.94/0.61    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f38,plain,(
% 1.94/0.61    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.94/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f37,f36,f35,f34,f33])).
% 1.94/0.61  fof(f33,plain,(
% 1.94/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f34,plain,(
% 1.94/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f35,plain,(
% 1.94/0.61    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,X2,X3,k2_tmap_1(sK0,sK1,X4,X2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,X2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f36,plain,(
% 1.94/0.61    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,X3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & sK0 = k1_tsep_1(sK0,sK2,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f37,plain,(
% 1.94/0.61    ? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),X4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,X4,sK2),k2_tmap_1(sK0,sK1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.94/0.61    introduced(choice_axiom,[])).
% 1.94/0.61  fof(f14,plain,(
% 1.94/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.94/0.61    inference(flattening,[],[f13])).
% 1.94/0.61  fof(f13,plain,(
% 1.94/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.94/0.61    inference(ennf_transformation,[],[f12])).
% 1.94/0.61  fof(f12,negated_conjecture,(
% 1.94/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.94/0.61    inference(negated_conjecture,[],[f11])).
% 1.94/0.61  fof(f11,conjecture,(
% 1.94/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.94/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).
% 1.94/0.61  fof(f145,plain,(
% 1.94/0.61    spl5_14),
% 1.94/0.61    inference(avatar_split_clause,[],[f54,f142])).
% 1.94/0.61  fof(f54,plain,(
% 1.94/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f140,plain,(
% 1.94/0.61    spl5_13),
% 1.94/0.61    inference(avatar_split_clause,[],[f53,f137])).
% 1.94/0.61  fof(f53,plain,(
% 1.94/0.61    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f135,plain,(
% 1.94/0.61    spl5_12),
% 1.94/0.61    inference(avatar_split_clause,[],[f51,f132])).
% 1.94/0.61  fof(f51,plain,(
% 1.94/0.61    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f130,plain,(
% 1.94/0.61    spl5_11),
% 1.94/0.61    inference(avatar_split_clause,[],[f50,f127])).
% 1.94/0.61  fof(f50,plain,(
% 1.94/0.61    m1_pre_topc(sK3,sK0)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f125,plain,(
% 1.94/0.61    spl5_10),
% 1.94/0.61    inference(avatar_split_clause,[],[f48,f122])).
% 1.94/0.61  fof(f48,plain,(
% 1.94/0.61    m1_pre_topc(sK2,sK0)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f120,plain,(
% 1.94/0.61    spl5_9),
% 1.94/0.61    inference(avatar_split_clause,[],[f52,f117])).
% 1.94/0.61  fof(f52,plain,(
% 1.94/0.61    v1_funct_1(sK4)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f115,plain,(
% 1.94/0.61    ~spl5_8),
% 1.94/0.61    inference(avatar_split_clause,[],[f49,f112])).
% 1.94/0.61  fof(f49,plain,(
% 1.94/0.61    ~v2_struct_0(sK3)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f110,plain,(
% 1.94/0.61    ~spl5_7),
% 1.94/0.61    inference(avatar_split_clause,[],[f47,f107])).
% 1.94/0.61  fof(f47,plain,(
% 1.94/0.61    ~v2_struct_0(sK2)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f105,plain,(
% 1.94/0.61    spl5_6),
% 1.94/0.61    inference(avatar_split_clause,[],[f46,f102])).
% 1.94/0.61  fof(f46,plain,(
% 1.94/0.61    l1_pre_topc(sK1)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f100,plain,(
% 1.94/0.61    spl5_5),
% 1.94/0.61    inference(avatar_split_clause,[],[f45,f97])).
% 1.94/0.61  fof(f45,plain,(
% 1.94/0.61    v2_pre_topc(sK1)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f95,plain,(
% 1.94/0.61    ~spl5_4),
% 1.94/0.61    inference(avatar_split_clause,[],[f44,f92])).
% 1.94/0.61  fof(f44,plain,(
% 1.94/0.61    ~v2_struct_0(sK1)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f90,plain,(
% 1.94/0.61    spl5_3),
% 1.94/0.61    inference(avatar_split_clause,[],[f43,f87])).
% 1.94/0.61  fof(f43,plain,(
% 1.94/0.61    l1_pre_topc(sK0)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f85,plain,(
% 1.94/0.61    spl5_2),
% 1.94/0.61    inference(avatar_split_clause,[],[f42,f82])).
% 1.94/0.61  fof(f42,plain,(
% 1.94/0.61    v2_pre_topc(sK0)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  fof(f80,plain,(
% 1.94/0.61    ~spl5_1),
% 1.94/0.61    inference(avatar_split_clause,[],[f41,f77])).
% 1.94/0.61  fof(f41,plain,(
% 1.94/0.61    ~v2_struct_0(sK0)),
% 1.94/0.61    inference(cnf_transformation,[],[f38])).
% 1.94/0.61  % SZS output end Proof for theBenchmark
% 1.94/0.61  % (6283)------------------------------
% 1.94/0.61  % (6283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.61  % (6283)Termination reason: Refutation
% 1.94/0.61  
% 1.94/0.61  % (6283)Memory used [KB]: 7164
% 1.94/0.61  % (6283)Time elapsed: 0.184 s
% 1.94/0.61  % (6283)------------------------------
% 1.94/0.61  % (6283)------------------------------
% 1.94/0.61  % (6280)Success in time 0.258 s
%------------------------------------------------------------------------------
