%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  257 ( 584 expanded)
%              Number of leaves         :   40 ( 241 expanded)
%              Depth                    :   19
%              Number of atoms          : 1360 (2278 expanded)
%              Number of equality atoms :  101 ( 171 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1480,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f119,f125,f133,f173,f217,f276,f341,f359,f365,f410,f442,f679,f776,f812,f841,f893,f1161,f1317,f1322,f1411,f1450,f1469,f1479])).

fof(f1479,plain,
    ( ~ spl6_4
    | spl6_73 ),
    inference(avatar_contradiction_clause,[],[f1478])).

fof(f1478,plain,
    ( $false
    | ~ spl6_4
    | spl6_73 ),
    inference(subsumption_resolution,[],[f1477,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1477,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_73 ),
    inference(resolution,[],[f1468,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1468,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_73 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1466,plain,
    ( spl6_73
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f1469,plain,
    ( ~ spl6_73
    | spl6_2
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1464,f492,f79,f1466])).

fof(f79,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f492,plain,
    ( spl6_28
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f1464,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_2
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1463,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1463,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(resolution,[],[f493,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f493,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1450,plain,
    ( ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | ~ spl6_45
    | spl6_68 ),
    inference(avatar_contradiction_clause,[],[f1449])).

fof(f1449,plain,
    ( $false
    | ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | ~ spl6_45
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1448,f340])).

fof(f340,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl6_17
  <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1448,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | ~ spl6_45
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1447,f840])).

fof(f840,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl6_41
  <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1447,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | ~ spl6_45
    | spl6_68 ),
    inference(resolution,[],[f1434,f892])).

fof(f892,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f890])).

fof(f890,plain,
    ( spl6_45
  <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1434,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) )
    | ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | ~ spl6_45
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1433,f892])).

fof(f1433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | ~ spl6_17
    | spl6_28
    | ~ spl6_41
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1432,f840])).

fof(f1432,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | ~ spl6_17
    | spl6_28
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1431,f340])).

fof(f1431,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_28
    | spl6_68 ),
    inference(subsumption_resolution,[],[f1430,f494])).

fof(f494,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1430,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | spl6_68 ),
    inference(duplicate_literal_removal,[],[f1429])).

fof(f1429,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_68 ),
    inference(resolution,[],[f1410,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
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
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f1410,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | spl6_68 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1408,plain,
    ( spl6_68
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1411,plain,
    ( ~ spl6_68
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | ~ spl6_45
    | spl6_58
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f1338,f1158,f1154,f890,f838,f412,f338,f273,f214,f94,f89,f84,f79,f1408])).

fof(f84,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f94,plain,
    ( spl6_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f214,plain,
    ( spl6_12
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f273,plain,
    ( spl6_14
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f412,plain,
    ( spl6_26
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1154,plain,
    ( spl6_58
  <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f1158,plain,
    ( spl6_59
  <=> u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f1338,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | ~ spl6_45
    | spl6_58
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1337,f892])).

fof(f1337,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | spl6_58
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1336,f414])).

fof(f414,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f412])).

fof(f1336,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | spl6_58
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1335,f840])).

fof(f1335,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | spl6_58
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1334,f414])).

fof(f1334,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_26
    | spl6_58
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1333,f414])).

fof(f1333,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_17
    | spl6_58
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1332,f275])).

fof(f275,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f1332,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_17
    | spl6_58
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1331,f216])).

fof(f216,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f214])).

fof(f1331,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | spl6_58
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1330,f1155])).

fof(f1155,plain,
    ( k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))
    | spl6_58 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1330,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1329,f96])).

fof(f96,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1329,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_pre_topc(sK1,sK0)
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1327,f340])).

fof(f1327,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_pre_topc(sK1,sK0)
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_59 ),
    inference(superposition,[],[f218,f1160])).

fof(f1160,plain,
    ( u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f218,plain,
    ( ! [X2,X3] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ m1_pre_topc(X2,sK0)
        | k9_tmap_1(sK0,X2) = X3 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f107,f91])).

fof(f107,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | k9_tmap_1(sK0,X2) = X3 )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f99,f81])).

fof(f99,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)))))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3)))
        | k9_tmap_1(sK0,X2) = X3 )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f56])).

% (27407)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f86,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1322,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f1321])).

fof(f1321,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_25
    | spl6_65 ),
    inference(subsumption_resolution,[],[f1320,f118])).

fof(f118,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1320,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_25
    | spl6_65 ),
    inference(resolution,[],[f1316,f423])).

fof(f423,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f422,f216])).

fof(f422,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl6_1
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f421,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f421,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f416,f96])).

fof(f416,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(superposition,[],[f199,f409])).

fof(f409,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl6_25
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f199,plain,
    ( ! [X10,X9] :
        ( r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10)
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f114,f91])).

fof(f114,plain,
    ( ! [X10,X9] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f113,plain,
    ( ! [X10,X9] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f105,f81])).

fof(f105,plain,
    ( ! [X10,X9] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10) )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) != X1
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

fof(f1316,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f1314,plain,
    ( spl6_65
  <=> r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1317,plain,
    ( ~ spl6_65
    | spl6_7
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f1177,f1154,f122,f1314])).

fof(f122,plain,
    ( spl6_7
  <=> r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1177,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)
    | spl6_7
    | ~ spl6_58 ),
    inference(superposition,[],[f124,f1156])).

fof(f1156,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f124,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1161,plain,
    ( spl6_58
    | spl6_59
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f1151,f890,f838,f412,f338,f94,f89,f84,f79,f1158,f1154])).

fof(f1151,plain,
    ( u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_41
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1150,f840])).

fof(f1150,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f1149,f340])).

fof(f1149,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_45 ),
    inference(resolution,[],[f461,f892])).

fof(f461,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK0))
        | u1_struct_0(sK1) = sK5(sK0,sK1,X3)
        | k9_tmap_1(sK0,sK1) = X3 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f446,f96])).

fof(f446,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_pre_topc(sK1,sK0)
        | u1_struct_0(sK1) = sK5(sK0,sK1,X3)
        | k9_tmap_1(sK0,sK1) = X3 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(superposition,[],[f212,f414])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(X0) = sK5(sK0,X0,X1)
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | u1_struct_0(X0) = sK5(sK0,X0,X1)
        | k9_tmap_1(sK0,X0) = X1 )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f98,f81])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)))))
        | u1_struct_0(X0) = sK5(sK0,X0,X1)
        | k9_tmap_1(sK0,X0) = X1 )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | u1_struct_0(X1) = sK5(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f893,plain,
    ( spl6_45
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f888,f412,f407,f334,f214,f89,f84,f79,f890])).

fof(f334,plain,
    ( spl6_16
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f888,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f440,f414])).

fof(f440,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f439,f216])).

fof(f439,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f438,f81])).

fof(f438,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f437,f335])).

fof(f335,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f334])).

fof(f437,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f436,f91])).

fof(f436,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f420,f86])).

fof(f420,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_25 ),
    inference(superposition,[],[f66,f409])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f841,plain,
    ( spl6_41
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f829,f809,f773,f676,f89,f84,f79,f838])).

fof(f676,plain,
    ( spl6_35
  <=> m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f773,plain,
    ( spl6_39
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f809,plain,
    ( spl6_40
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f829,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35
    | ~ spl6_39
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f828,f775])).

fof(f775,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f773])).

fof(f828,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f827,f81])).

fof(f827,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f826,f678])).

fof(f678,plain,
    ( m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f676])).

fof(f826,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | ~ m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f825,f91])).

fof(f825,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f818,f86])).

fof(f818,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_40 ),
    inference(superposition,[],[f65,f811])).

fof(f811,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f809])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f812,plain,
    ( spl6_40
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f682,f676,f89,f84,f79,f809])).

fof(f682,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35 ),
    inference(resolution,[],[f678,f145])).

fof(f145,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f108,f91])).

fof(f108,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f100,f81])).

fof(f100,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f776,plain,
    ( spl6_39
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f681,f676,f89,f84,f79,f773])).

fof(f681,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_35 ),
    inference(resolution,[],[f678,f168])).

fof(f168,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f109,f91])).

fof(f109,plain,
    ( ! [X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f101,f81])).

fof(f101,plain,
    ( ! [X5] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f679,plain,
    ( spl6_35
    | ~ spl6_19
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f670,f412,f346,f676])).

fof(f346,plain,
    ( spl6_19
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f670,plain,
    ( m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_19
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f669,f347])).

fof(f347,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f346])).

fof(f669,plain,
    ( m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_19
    | ~ spl6_26 ),
    inference(resolution,[],[f469,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_pre_topc)).

fof(f469,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
        | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_19
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f448,f347])).

fof(f448,plain,
    ( ! [X4] :
        ( m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X4,k8_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) )
    | ~ spl6_26 ),
    inference(superposition,[],[f46,f414])).

fof(f442,plain,
    ( spl6_26
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f415,f407,f273,f412])).

fof(f415,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(superposition,[],[f275,f409])).

fof(f410,plain,
    ( spl6_25
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f395,f346,f334,f170,f130,f94,f89,f84,f79,f407])).

fof(f130,plain,
    ( spl6_8
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f170,plain,
    ( spl6_10
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f395,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f394,f335])).

fof(f394,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f393,f347])).

fof(f393,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f144,f172])).

fof(f172,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f144,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f143,f81])).

fof(f143,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f142,f96])).

fof(f142,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f141,f91])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f138,f86])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f132,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f132,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f365,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_16 ),
    inference(subsumption_resolution,[],[f363,f91])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_5
    | spl6_16 ),
    inference(subsumption_resolution,[],[f362,f96])).

fof(f362,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_16 ),
    inference(resolution,[],[f336,f46])).

fof(f336,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f334])).

fof(f359,plain,
    ( spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(subsumption_resolution,[],[f357,f81])).

fof(f357,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(subsumption_resolution,[],[f356,f96])).

fof(f356,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | spl6_19 ),
    inference(subsumption_resolution,[],[f355,f91])).

fof(f355,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | spl6_19 ),
    inference(subsumption_resolution,[],[f354,f86])).

fof(f354,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | spl6_19 ),
    inference(resolution,[],[f348,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f348,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f346])).

fof(f341,plain,
    ( ~ spl6_16
    | spl6_17
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f232,f214,f89,f84,f79,f338,f334])).

fof(f232,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f231,f81])).

fof(f231,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f230,f91])).

fof(f230,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f221,f86])).

fof(f221,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_12 ),
    inference(superposition,[],[f64,f216])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f276,plain,
    ( spl6_14
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f245,f94,f89,f84,f79,f273])).

fof(f245,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f177,f96])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f174,f91])).

fof(f174,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f168,f46])).

fof(f217,plain,
    ( spl6_12
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f210,f94,f89,f84,f79,f214])).

fof(f210,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f154,f96])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f151,f91])).

fof(f151,plain,
    ( ! [X0] :
        ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f145,f46])).

fof(f173,plain,
    ( spl6_10
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f136,f94,f89,f84,f79,f170])).

fof(f136,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f134,f96])).

fof(f134,plain,
    ( ! [X8] :
        ( ~ m1_pre_topc(X8,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X8)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f112,f91])).

fof(f112,plain,
    ( ! [X8] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X8,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X8)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f104,f81])).

fof(f104,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X8,sK0)
        | v2_pre_topc(k8_tmap_1(sK0,X8)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,
    ( spl6_8
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f127,f94,f89,f84,f79,f130])).

fof(f127,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f120,f96])).

fof(f120,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(X7,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X7)) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f111,f91])).

fof(f111,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X7,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X7)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f103,f81])).

fof(f103,plain,
    ( ! [X7] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X7,sK0)
        | v1_pre_topc(k8_tmap_1(sK0,X7)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f86,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f39,f122])).

fof(f39,plain,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

fof(f119,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f38,f116])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f42,f79])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f40,f74])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27410)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.45  % (27424)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (27418)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (27409)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (27416)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (27417)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (27408)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (27408)Refutation not found, incomplete strategy% (27408)------------------------------
% 0.20/0.48  % (27408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27408)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (27408)Memory used [KB]: 10618
% 0.20/0.48  % (27408)Time elapsed: 0.068 s
% 0.20/0.48  % (27408)------------------------------
% 0.20/0.48  % (27408)------------------------------
% 0.20/0.50  % (27412)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (27426)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (27422)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (27425)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (27410)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1480,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f119,f125,f133,f173,f217,f276,f341,f359,f365,f410,f442,f679,f776,f812,f841,f893,f1161,f1317,f1322,f1411,f1450,f1469,f1479])).
% 0.20/0.51  fof(f1479,plain,(
% 0.20/0.51    ~spl6_4 | spl6_73),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1478])).
% 0.20/0.51  fof(f1478,plain,(
% 0.20/0.51    $false | (~spl6_4 | spl6_73)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1477,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl6_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f1477,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | spl6_73),
% 0.20/0.51    inference(resolution,[],[f1468,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f1468,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | spl6_73),
% 0.20/0.51    inference(avatar_component_clause,[],[f1466])).
% 0.20/0.51  fof(f1466,plain,(
% 0.20/0.51    spl6_73 <=> l1_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 0.20/0.51  fof(f1469,plain,(
% 0.20/0.51    ~spl6_73 | spl6_2 | ~spl6_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f1464,f492,f79,f1466])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl6_2 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f492,plain,(
% 0.20/0.51    spl6_28 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.51  fof(f1464,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | (spl6_2 | ~spl6_28)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1463,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f79])).
% 0.20/0.51  fof(f1463,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_28),
% 0.20/0.51    inference(resolution,[],[f493,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.51  fof(f493,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f492])).
% 0.20/0.51  fof(f1450,plain,(
% 0.20/0.51    ~spl6_17 | spl6_28 | ~spl6_41 | ~spl6_45 | spl6_68),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1449])).
% 0.20/0.51  fof(f1449,plain,(
% 0.20/0.51    $false | (~spl6_17 | spl6_28 | ~spl6_41 | ~spl6_45 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1448,f340])).
% 0.20/0.51  fof(f340,plain,(
% 0.20/0.51    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~spl6_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f338])).
% 0.20/0.51  fof(f338,plain,(
% 0.20/0.51    spl6_17 <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.51  fof(f1448,plain,(
% 0.20/0.51    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl6_17 | spl6_28 | ~spl6_41 | ~spl6_45 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1447,f840])).
% 0.20/0.51  fof(f840,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_41),
% 0.20/0.51    inference(avatar_component_clause,[],[f838])).
% 0.20/0.51  fof(f838,plain,(
% 0.20/0.51    spl6_41 <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.51  fof(f1447,plain,(
% 0.20/0.51    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl6_17 | spl6_28 | ~spl6_41 | ~spl6_45 | spl6_68)),
% 0.20/0.51    inference(resolution,[],[f1434,f892])).
% 0.20/0.51  fof(f892,plain,(
% 0.20/0.51    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_45),
% 0.20/0.51    inference(avatar_component_clause,[],[f890])).
% 0.20/0.51  fof(f890,plain,(
% 0.20/0.51    spl6_45 <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.20/0.51  fof(f1434,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0)) ) | (~spl6_17 | spl6_28 | ~spl6_41 | ~spl6_45 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1433,f892])).
% 0.20/0.51  fof(f1433,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (~spl6_17 | spl6_28 | ~spl6_41 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1432,f840])).
% 0.20/0.51  fof(f1432,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (~spl6_17 | spl6_28 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1431,f340])).
% 0.20/0.51  fof(f1431,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (spl6_28 | spl6_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1430,f494])).
% 0.20/0.51  fof(f494,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f492])).
% 0.20/0.51  fof(f1430,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | spl6_68),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f1429])).
% 0.20/0.51  fof(f1429,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK0))) ) | spl6_68),
% 0.20/0.51    inference(resolution,[],[f1410,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 0.20/0.51  fof(f1410,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | spl6_68),
% 0.20/0.51    inference(avatar_component_clause,[],[f1408])).
% 0.20/0.51  fof(f1408,plain,(
% 0.20/0.51    spl6_68 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.20/0.51  fof(f1411,plain,(
% 0.20/0.51    ~spl6_68 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | ~spl6_41 | ~spl6_45 | spl6_58 | ~spl6_59),
% 0.20/0.51    inference(avatar_split_clause,[],[f1338,f1158,f1154,f890,f838,f412,f338,f273,f214,f94,f89,f84,f79,f1408])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl6_3 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl6_5 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    spl6_12 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    spl6_14 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.51  fof(f412,plain,(
% 0.20/0.51    spl6_26 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.51  fof(f1154,plain,(
% 0.20/0.51    spl6_58 <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.20/0.51  fof(f1158,plain,(
% 0.20/0.51    spl6_59 <=> u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.20/0.51  fof(f1338,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | ~spl6_41 | ~spl6_45 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1337,f892])).
% 0.20/0.51  fof(f1337,plain,(
% 0.20/0.51    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | ~spl6_41 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f1336,f414])).
% 0.20/0.51  fof(f414,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f412])).
% 0.20/0.51  fof(f1336,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | ~spl6_41 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1335,f840])).
% 0.20/0.51  fof(f1335,plain,(
% 0.20/0.51    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f1334,f414])).
% 0.20/0.51  fof(f1334,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | ~spl6_26 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f1333,f414])).
% 0.20/0.51  fof(f1333,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_14 | ~spl6_17 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f1332,f275])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f273])).
% 0.20/0.51  fof(f1332,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_17 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(forward_demodulation,[],[f1331,f216])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f214])).
% 0.20/0.51  fof(f1331,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | spl6_58 | ~spl6_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1330,f1155])).
% 0.20/0.51  fof(f1155,plain,(
% 0.20/0.51    k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) | spl6_58),
% 0.20/0.51    inference(avatar_component_clause,[],[f1154])).
% 0.20/0.51  fof(f1330,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1329,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    m1_pre_topc(sK1,sK0) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f94])).
% 0.20/0.51  fof(f1329,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_pre_topc(sK1,sK0) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17 | ~spl6_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1327,f340])).
% 0.20/0.51  fof(f1327,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_pre_topc(sK1,sK0) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_59)),
% 0.20/0.51    inference(superposition,[],[f218,f1160])).
% 0.20/0.51  fof(f1160,plain,(
% 0.20/0.51    u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | ~spl6_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f1158])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~m1_pre_topc(X2,sK0) | k9_tmap_1(sK0,X2) = X3) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f107,f91])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | k9_tmap_1(sK0,X2) = X3) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f81])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2))))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X2)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X2,X3))),X3,k7_tmap_1(sK0,sK5(sK0,X2,X3))) | k9_tmap_1(sK0,X2) = X3) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f56])).
% 0.20/0.51  % (27407)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) | k9_tmap_1(X0,X1) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f1322,plain,(
% 0.20/0.51    spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_25 | spl6_65),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1321])).
% 0.20/0.51  fof(f1321,plain,(
% 0.20/0.51    $false | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_25 | spl6_65)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1320,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl6_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f1320,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,u1_struct_0(sK1)) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_25 | spl6_65)),
% 0.20/0.51    inference(resolution,[],[f1316,f423])).
% 0.20/0.51  fof(f423,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_25)),
% 0.20/0.51    inference(forward_demodulation,[],[f422,f216])).
% 0.20/0.51  fof(f422,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (spl6_1 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f421,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~v2_struct_0(sK1) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl6_1 <=> v2_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f421,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f416,f96])).
% 0.20/0.51  fof(f416,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_25)),
% 0.20/0.51    inference(superposition,[],[f199,f409])).
% 0.20/0.51  fof(f409,plain,(
% 0.20/0.51    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f407])).
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    spl6_25 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ( ! [X10,X9] : (r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10) | ~m1_pre_topc(X9,sK0) | ~m1_subset_1(X10,u1_struct_0(X9)) | v2_struct_0(X9)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f114,f91])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X10,X9] : (~l1_pre_topc(sK0) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | ~m1_subset_1(X10,u1_struct_0(X9)) | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10)) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X10,X9] : (~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | ~m1_subset_1(X10,u1_struct_0(X9)) | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10)) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f81])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X10,X9] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(X9),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | ~m1_subset_1(X10,u1_struct_0(X9)) | r1_tmap_1(X9,k6_tmap_1(sK0,u1_struct_0(X9)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X9)),k7_tmap_1(sK0,u1_struct_0(X9)),X9),X10)) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) != X1 | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).
% 0.20/0.51  fof(f1316,plain,(
% 0.20/0.51    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | spl6_65),
% 0.20/0.51    inference(avatar_component_clause,[],[f1314])).
% 0.20/0.51  fof(f1314,plain,(
% 0.20/0.51    spl6_65 <=> r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.20/0.51  fof(f1317,plain,(
% 0.20/0.51    ~spl6_65 | spl6_7 | ~spl6_58),
% 0.20/0.51    inference(avatar_split_clause,[],[f1177,f1154,f122,f1314])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl6_7 <=> r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.51  fof(f1177,plain,(
% 0.20/0.51    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) | (spl6_7 | ~spl6_58)),
% 0.20/0.51    inference(superposition,[],[f124,f1156])).
% 0.20/0.51  fof(f1156,plain,(
% 0.20/0.51    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~spl6_58),
% 0.20/0.51    inference(avatar_component_clause,[],[f1154])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) | spl6_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f1161,plain,(
% 0.20/0.51    spl6_58 | spl6_59 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_26 | ~spl6_41 | ~spl6_45),
% 0.20/0.51    inference(avatar_split_clause,[],[f1151,f890,f838,f412,f338,f94,f89,f84,f79,f1158,f1154])).
% 0.20/0.51  fof(f1151,plain,(
% 0.20/0.51    u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_26 | ~spl6_41 | ~spl6_45)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1150,f840])).
% 0.20/0.51  fof(f1150,plain,(
% 0.20/0.51    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_26 | ~spl6_45)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1149,f340])).
% 0.20/0.51  fof(f1149,plain,(
% 0.20/0.51    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26 | ~spl6_45)),
% 0.20/0.51    inference(resolution,[],[f461,f892])).
% 0.20/0.51  fof(f461,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK5(sK0,sK1,X3) | k9_tmap_1(sK0,sK1) = X3) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f446,f96])).
% 0.20/0.51  fof(f446,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | u1_struct_0(sK1) = sK5(sK0,sK1,X3) | k9_tmap_1(sK0,sK1) = X3) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_26)),
% 0.20/0.51    inference(superposition,[],[f212,f414])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = sK5(sK0,X0,X1) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f106,f91])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | u1_struct_0(X0) = sK5(sK0,X0,X1) | k9_tmap_1(sK0,X0) = X1) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f98,f81])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0))))) | u1_struct_0(X0) = sK5(sK0,X0,X1) | k9_tmap_1(sK0,X0) = X1) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | u1_struct_0(X1) = sK5(X0,X1,X2) | k9_tmap_1(X0,X1) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f893,plain,(
% 0.20/0.51    spl6_45 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f888,f412,f407,f334,f214,f89,f84,f79,f890])).
% 0.20/0.51  fof(f334,plain,(
% 0.20/0.51    spl6_16 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.51  fof(f888,plain,(
% 0.20/0.51    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_26)),
% 0.20/0.51    inference(forward_demodulation,[],[f440,f414])).
% 0.20/0.51  fof(f440,plain,(
% 0.20/0.51    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_12 | ~spl6_16 | ~spl6_25)),
% 0.20/0.51    inference(forward_demodulation,[],[f439,f216])).
% 0.20/0.51  fof(f439,plain,(
% 0.20/0.51    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f438,f81])).
% 0.20/0.51  fof(f438,plain,(
% 0.20/0.51    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f437,f335])).
% 0.20/0.51  fof(f335,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f334])).
% 0.20/0.51  fof(f437,plain,(
% 0.20/0.51    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f436,f91])).
% 0.20/0.51  fof(f436,plain,(
% 0.20/0.51    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f420,f86])).
% 0.20/0.51  fof(f420,plain,(
% 0.20/0.51    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_25),
% 0.20/0.51    inference(superposition,[],[f66,f409])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.20/0.51  fof(f841,plain,(
% 0.20/0.51    spl6_41 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35 | ~spl6_39 | ~spl6_40),
% 0.20/0.51    inference(avatar_split_clause,[],[f829,f809,f773,f676,f89,f84,f79,f838])).
% 0.20/0.51  fof(f676,plain,(
% 0.20/0.51    spl6_35 <=> m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.51  fof(f773,plain,(
% 0.20/0.51    spl6_39 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.51  fof(f809,plain,(
% 0.20/0.51    spl6_40 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.51  fof(f829,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35 | ~spl6_39 | ~spl6_40)),
% 0.20/0.51    inference(forward_demodulation,[],[f828,f775])).
% 0.20/0.51  fof(f775,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))) | ~spl6_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f773])).
% 0.20/0.51  fof(f828,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35 | ~spl6_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f827,f81])).
% 0.20/0.51  fof(f827,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_35 | ~spl6_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f826,f678])).
% 0.20/0.51  fof(f678,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_35),
% 0.20/0.51    inference(avatar_component_clause,[],[f676])).
% 0.20/0.51  fof(f826,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | ~m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f825,f91])).
% 0.20/0.51  fof(f825,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f818,f86])).
% 0.20/0.51  fof(f818,plain,(
% 0.20/0.51    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_40),
% 0.20/0.51    inference(superposition,[],[f65,f811])).
% 0.20/0.51  fof(f811,plain,(
% 0.20/0.51    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))) | ~spl6_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f809])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f812,plain,(
% 0.20/0.51    spl6_40 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35),
% 0.20/0.51    inference(avatar_split_clause,[],[f682,f676,f89,f84,f79,f809])).
% 0.20/0.51  fof(f682,plain,(
% 0.20/0.51    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1)))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35)),
% 0.20/0.51    inference(resolution,[],[f678,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f108,f91])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f81])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X4] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X4) = k6_partfun1(u1_struct_0(sK0))) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 0.20/0.51  fof(f776,plain,(
% 0.20/0.51    spl6_39 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35),
% 0.20/0.51    inference(avatar_split_clause,[],[f681,f676,f89,f84,f79,f773])).
% 0.20/0.51  fof(f681,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK3(k8_tmap_1(sK0,sK1))))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_35)),
% 0.20/0.51    inference(resolution,[],[f678,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f109,f91])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f81])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X5))) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.51  fof(f679,plain,(
% 0.20/0.51    spl6_35 | ~spl6_19 | ~spl6_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f670,f412,f346,f676])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    spl6_19 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.51  fof(f670,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_19 | ~spl6_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f669,f347])).
% 0.20/0.51  fof(f347,plain,(
% 0.20/0.51    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f346])).
% 0.20/0.51  fof(f669,plain,(
% 0.20/0.51    m1_subset_1(u1_struct_0(sK3(k8_tmap_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl6_19 | ~spl6_26)),
% 0.20/0.51    inference(resolution,[],[f469,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (m1_pre_topc(sK3(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ? [X1] : m1_pre_topc(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_pre_topc)).
% 0.20/0.51  fof(f469,plain,(
% 0.20/0.51    ( ! [X4] : (~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_19 | ~spl6_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f448,f347])).
% 0.20/0.51  fof(f448,plain,(
% 0.20/0.51    ( ! [X4] : (m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X4,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))) ) | ~spl6_26),
% 0.20/0.51    inference(superposition,[],[f46,f414])).
% 0.20/0.51  fof(f442,plain,(
% 0.20/0.51    spl6_26 | ~spl6_14 | ~spl6_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f415,f407,f273,f412])).
% 0.20/0.51  fof(f415,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl6_14 | ~spl6_25)),
% 0.20/0.51    inference(superposition,[],[f275,f409])).
% 0.20/0.51  fof(f410,plain,(
% 0.20/0.51    spl6_25 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_16 | ~spl6_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f395,f346,f334,f170,f130,f94,f89,f84,f79,f407])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl6_8 <=> v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl6_10 <=> v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_16 | ~spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f394,f335])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f393,f347])).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f172])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f170])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f143,f81])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f142,f96])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_3 | ~spl6_4 | ~spl6_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f141,f91])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_3 | ~spl6_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f86])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_8),
% 0.20/0.51    inference(resolution,[],[f132,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.20/0.51    inference(equality_resolution,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl6_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f130])).
% 0.20/0.51  fof(f365,plain,(
% 0.20/0.51    ~spl6_4 | ~spl6_5 | spl6_16),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f364])).
% 0.20/0.51  fof(f364,plain,(
% 0.20/0.51    $false | (~spl6_4 | ~spl6_5 | spl6_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f363,f91])).
% 0.20/0.51  fof(f363,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | (~spl6_5 | spl6_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f362,f96])).
% 0.20/0.51  fof(f362,plain,(
% 0.20/0.51    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_16),
% 0.20/0.51    inference(resolution,[],[f336,f46])).
% 0.20/0.51  fof(f336,plain,(
% 0.20/0.51    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f334])).
% 0.20/0.51  fof(f359,plain,(
% 0.20/0.51    spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f358])).
% 0.20/0.51  fof(f358,plain,(
% 0.20/0.51    $false | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f357,f81])).
% 0.20/0.51  fof(f357,plain,(
% 0.20/0.51    v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f356,f96])).
% 0.20/0.51  fof(f356,plain,(
% 0.20/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f355,f91])).
% 0.20/0.51  fof(f355,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl6_3 | spl6_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f354,f86])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | spl6_19),
% 0.20/0.51    inference(resolution,[],[f348,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | spl6_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f346])).
% 0.20/0.51  fof(f341,plain,(
% 0.20/0.51    ~spl6_16 | spl6_17 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f232,f214,f89,f84,f79,f338,f334])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_12)),
% 0.20/0.51    inference(subsumption_resolution,[],[f231,f81])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_12)),
% 0.20/0.51    inference(subsumption_resolution,[],[f230,f91])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_12)),
% 0.20/0.51    inference(subsumption_resolution,[],[f221,f86])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl6_12),
% 0.20/0.51    inference(superposition,[],[f64,f216])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    spl6_14 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f245,f94,f89,f84,f79,f273])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f177,f96])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f174,f91])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(resolution,[],[f168,f46])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    spl6_12 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f210,f94,f89,f84,f79,f214])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f154,f96])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f151,f91])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ( ! [X0] : (k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(resolution,[],[f145,f46])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    spl6_10 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f136,f94,f89,f84,f79,f170])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    v2_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f134,f96])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X8] : (~m1_pre_topc(X8,sK0) | v2_pre_topc(k8_tmap_1(sK0,X8))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f91])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X8] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X8,sK0) | v2_pre_topc(k8_tmap_1(sK0,X8))) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f104,f81])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X8] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X8,sK0) | v2_pre_topc(k8_tmap_1(sK0,X8))) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl6_8 | spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f127,f94,f89,f84,f79,f130])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    v1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.20/0.51    inference(resolution,[],[f120,f96])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X7] : (~m1_pre_topc(X7,sK0) | v1_pre_topc(k8_tmap_1(sK0,X7))) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f91])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X7,sK0) | v1_pre_topc(k8_tmap_1(sK0,X7))) ) | (spl6_2 | ~spl6_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f81])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X7] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X7,sK0) | v1_pre_topc(k8_tmap_1(sK0,X7))) ) | ~spl6_3),
% 0.20/0.51    inference(resolution,[],[f86,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ~spl6_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f122])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl6_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f116])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f94])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    m1_pre_topc(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f89])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl6_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f84])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f79])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f74])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ~v2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27410)------------------------------
% 0.20/0.51  % (27410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27410)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27410)Memory used [KB]: 11385
% 0.20/0.51  % (27410)Time elapsed: 0.110 s
% 0.20/0.51  % (27410)------------------------------
% 0.20/0.51  % (27410)------------------------------
% 0.20/0.51  % (27411)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (27406)Success in time 0.155 s
%------------------------------------------------------------------------------
