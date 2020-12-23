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
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 335 expanded)
%              Number of leaves         :   49 ( 160 expanded)
%              Depth                    :    7
%              Number of atoms          :  504 ( 886 expanded)
%              Number of equality atoms :   85 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f79,f83,f88,f93,f97,f101,f105,f109,f123,f127,f145,f161,f177,f228,f237,f253,f259,f265,f274,f285,f313,f551,f773,f1337,f1401,f1410,f1447,f1864,f2025,f2538,f3060,f3100,f3136,f3523])).

fof(f3523,plain,
    ( ~ spl2_5
    | spl2_19
    | ~ spl2_108 ),
    inference(avatar_contradiction_clause,[],[f3514])).

fof(f3514,plain,
    ( $false
    | ~ spl2_5
    | spl2_19
    | ~ spl2_108 ),
    inference(subsumption_resolution,[],[f160,f3458])).

fof(f3458,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)
    | ~ spl2_5
    | ~ spl2_108 ),
    inference(superposition,[],[f3135,f78])).

fof(f78,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_5
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3135,plain,
    ( ! [X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0)
    | ~ spl2_108 ),
    inference(avatar_component_clause,[],[f3134])).

fof(f3134,plain,
    ( spl2_108
  <=> ! [X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f160,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl2_19
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f3136,plain,
    ( spl2_108
    | ~ spl2_11
    | ~ spl2_105 ),
    inference(avatar_split_clause,[],[f3103,f3098,f103,f3134])).

fof(f103,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f3098,plain,
    ( spl2_105
  <=> ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f3103,plain,
    ( ! [X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0)
    | ~ spl2_11
    | ~ spl2_105 ),
    inference(resolution,[],[f3099,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f3099,plain,
    ( ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)
    | ~ spl2_105 ),
    inference(avatar_component_clause,[],[f3098])).

fof(f3100,plain,
    ( spl2_105
    | ~ spl2_44
    | ~ spl2_67
    | ~ spl2_82
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f3096,f3058,f2023,f1444,f549,f3098])).

fof(f549,plain,
    ( spl2_44
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1444,plain,
    ( spl2_67
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f2023,plain,
    ( spl2_82
  <=> ! [X13,X14] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f3058,plain,
    ( spl2_104
  <=> ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f3096,plain,
    ( ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)
    | ~ spl2_44
    | ~ spl2_67
    | ~ spl2_82
    | ~ spl2_104 ),
    inference(forward_demodulation,[],[f3095,f1446])).

fof(f1446,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f3095,plain,
    ( ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_44
    | ~ spl2_82
    | ~ spl2_104 ),
    inference(subsumption_resolution,[],[f3078,f2024])).

fof(f2024,plain,
    ( ! [X14,X13] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f2023])).

fof(f3078,plain,
    ( ! [X10] :
        ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))
        | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1)) )
    | ~ spl2_44
    | ~ spl2_104 ),
    inference(superposition,[],[f550,f3059])).

fof(f3059,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f3058])).

fof(f550,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f549])).

fof(f3060,plain,
    ( spl2_104
    | ~ spl2_32
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f2772,f2536,f263,f3058])).

fof(f263,plain,
    ( spl2_32
  <=> ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f2536,plain,
    ( spl2_99
  <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f2772,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))
    | ~ spl2_32
    | ~ spl2_99 ),
    inference(superposition,[],[f2537,f264])).

fof(f264,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f263])).

fof(f2537,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f2536])).

fof(f2538,plain,
    ( spl2_99
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f2144,f1862,f68,f63,f58,f2536])).

fof(f58,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f68,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1862,plain,
    ( spl2_76
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f2144,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f2143,f60])).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f2143,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(subsumption_resolution,[],[f2142,f65])).

fof(f65,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f2142,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_76 ),
    inference(resolution,[],[f1863,f70])).

fof(f70,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f1863,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f1862])).

fof(f2025,plain,
    ( spl2_82
    | ~ spl2_36
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f1971,f1399,f311,f2023])).

fof(f311,plain,
    ( spl2_36
  <=> ! [X9,X11,X10] : r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f1399,plain,
    ( spl2_65
  <=> ! [X34] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f1971,plain,
    ( ! [X14,X13] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1))
    | ~ spl2_36
    | ~ spl2_65 ),
    inference(superposition,[],[f312,f1400])).

fof(f1400,plain,
    ( ! [X34] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f1399])).

fof(f312,plain,
    ( ! [X10,X11,X9] : r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f1864,plain,(
    spl2_76 ),
    inference(avatar_split_clause,[],[f50,f1862])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f1447,plain,
    ( spl2_67
    | ~ spl2_15
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f1436,f1408,f125,f1444])).

fof(f125,plain,
    ( spl2_15
  <=> ! [X3] : k1_xboole_0 = k6_subset_1(X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f1408,plain,
    ( spl2_66
  <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f1436,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_15
    | ~ spl2_66 ),
    inference(forward_demodulation,[],[f1413,f126])).

fof(f126,plain,
    ( ! [X3] : k1_xboole_0 = k6_subset_1(X3,X3)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1413,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))
    | ~ spl2_15
    | ~ spl2_66 ),
    inference(superposition,[],[f1409,f126])).

fof(f1409,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1410,plain,
    ( spl2_66
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f1403,f771,f63,f58,f1408])).

fof(f771,plain,
    ( spl2_55
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f1403,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(subsumption_resolution,[],[f1402,f60])).

fof(f1402,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_55 ),
    inference(resolution,[],[f772,f65])).

fof(f772,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f771])).

fof(f1401,plain,
    ( spl2_65
    | ~ spl2_28
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f1362,f1335,f235,f1399])).

fof(f235,plain,
    ( spl2_28
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1335,plain,
    ( spl2_61
  <=> ! [X5,X4] :
        ( k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5
        | k1_xboole_0 != k6_subset_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f1362,plain,
    ( ! [X34] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))
    | ~ spl2_28
    | ~ spl2_61 ),
    inference(trivial_inequality_removal,[],[f1355])).

fof(f1355,plain,
    ( ! [X34] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34))) )
    | ~ spl2_28
    | ~ spl2_61 ),
    inference(superposition,[],[f1336,f236])).

fof(f236,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f235])).

fof(f1336,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k6_subset_1(X4,X5)
        | k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5 )
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1337,plain,
    ( spl2_61
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f185,f175,f107,f1335])).

fof(f107,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f175,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f185,plain,
    ( ! [X4,X5] :
        ( k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5
        | k1_xboole_0 != k6_subset_1(X4,X5) )
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(resolution,[],[f176,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f773,plain,(
    spl2_55 ),
    inference(avatar_split_clause,[],[f49,f771])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f551,plain,
    ( spl2_44
    | ~ spl2_1
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f547,f272,f58,f549])).

fof(f272,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_1
    | ~ spl2_33 ),
    inference(resolution,[],[f273,f60])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f272])).

fof(f313,plain,
    ( spl2_36
    | ~ spl2_17
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f298,f283,f143,f311])).

fof(f143,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f283,plain,
    ( spl2_35
  <=> ! [X1,X2] : k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f298,plain,
    ( ! [X10,X11,X9] : r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11))
    | ~ spl2_17
    | ~ spl2_35 ),
    inference(superposition,[],[f144,f284])).

fof(f284,plain,
    ( ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f283])).

fof(f144,plain,
    ( ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f285,plain,
    ( spl2_35
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f183,f175,f81,f283])).

fof(f81,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f183,plain,
    ( ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1
    | ~ spl2_6
    | ~ spl2_22 ),
    inference(resolution,[],[f176,f82])).

fof(f82,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f274,plain,(
    spl2_33 ),
    inference(avatar_split_clause,[],[f42,f272])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f265,plain,
    ( spl2_32
    | ~ spl2_11
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f261,f257,f103,f263])).

fof(f257,plain,
    ( spl2_31
  <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f261,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)
    | ~ spl2_11
    | ~ spl2_31 ),
    inference(resolution,[],[f258,f104])).

fof(f258,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl2_31
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f255,f251,f63,f58,f257])).

fof(f251,plain,
    ( spl2_30
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f255,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f254,f60])).

fof(f254,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(resolution,[],[f252,f65])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f44,f251])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f237,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f233,f226,f58,f235])).

fof(f226,plain,
    ( spl2_26
  <=> ! [X5,X4] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f233,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_26 ),
    inference(resolution,[],[f227,f60])).

fof(f227,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X4)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,
    ( spl2_26
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f114,f103,f95,f226])).

fof(f95,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f114,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4))
        | ~ v1_relat_1(X4) )
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(resolution,[],[f104,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f177,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f53,f175])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f161,plain,
    ( ~ spl2_19
    | spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f154,f107,f90,f158])).

fof(f90,plain,
    ( spl2_8
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f154,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f108,f92])).

fof(f92,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f145,plain,
    ( spl2_17
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f128,f121,f99,f143])).

fof(f99,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f121,plain,
    ( spl2_14
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f128,plain,
    ( ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(resolution,[],[f122,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f122,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f127,plain,
    ( spl2_15
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f113,f103,f86,f125])).

fof(f86,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f113,plain,
    ( ! [X3] : k1_xboole_0 = k6_subset_1(X3,X3)
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(resolution,[],[f104,f87])).

fof(f87,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f123,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f110,f99,f86,f121])).

fof(f110,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(resolution,[],[f100,f87])).

fof(f109,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f105,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f97,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f41,f95])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f93,plain,(
    ~ spl2_8 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f88,plain,
    ( spl2_7
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f84,f81,f77,f86])).

fof(f84,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f82,f78])).

fof(f83,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f52,f81])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f51,f77])).

fof(f51,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f71,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (32608)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (32613)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (32610)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (32605)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (32614)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (32604)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (32606)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (32616)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (32602)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (32603)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (32611)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (32601)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (32609)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (32607)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32615)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.34/0.52  % (32612)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.34/0.52  % (32608)Refutation found. Thanks to Tanya!
% 1.34/0.52  % SZS status Theorem for theBenchmark
% 1.34/0.52  % SZS output start Proof for theBenchmark
% 1.34/0.52  fof(f3553,plain,(
% 1.34/0.52    $false),
% 1.34/0.52    inference(avatar_sat_refutation,[],[f61,f66,f71,f79,f83,f88,f93,f97,f101,f105,f109,f123,f127,f145,f161,f177,f228,f237,f253,f259,f265,f274,f285,f313,f551,f773,f1337,f1401,f1410,f1447,f1864,f2025,f2538,f3060,f3100,f3136,f3523])).
% 1.34/0.52  fof(f3523,plain,(
% 1.34/0.52    ~spl2_5 | spl2_19 | ~spl2_108),
% 1.34/0.52    inference(avatar_contradiction_clause,[],[f3514])).
% 1.34/0.52  fof(f3514,plain,(
% 1.34/0.52    $false | (~spl2_5 | spl2_19 | ~spl2_108)),
% 1.34/0.52    inference(subsumption_resolution,[],[f160,f3458])).
% 1.34/0.52  fof(f3458,plain,(
% 1.34/0.52    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ) | (~spl2_5 | ~spl2_108)),
% 1.34/0.52    inference(superposition,[],[f3135,f78])).
% 1.34/0.52  fof(f78,plain,(
% 1.34/0.52    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_5),
% 1.34/0.52    inference(avatar_component_clause,[],[f77])).
% 1.34/0.52  fof(f77,plain,(
% 1.34/0.52    spl2_5 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.34/0.52  fof(f3135,plain,(
% 1.34/0.52    ( ! [X3] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0)) ) | ~spl2_108),
% 1.34/0.52    inference(avatar_component_clause,[],[f3134])).
% 1.34/0.52  fof(f3134,plain,(
% 1.34/0.52    spl2_108 <=> ! [X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 1.34/0.52  fof(f160,plain,(
% 1.34/0.52    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_19),
% 1.34/0.52    inference(avatar_component_clause,[],[f158])).
% 1.34/0.52  fof(f158,plain,(
% 1.34/0.52    spl2_19 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.34/0.52  fof(f3136,plain,(
% 1.34/0.52    spl2_108 | ~spl2_11 | ~spl2_105),
% 1.34/0.52    inference(avatar_split_clause,[],[f3103,f3098,f103,f3134])).
% 1.34/0.52  fof(f103,plain,(
% 1.34/0.52    spl2_11 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.34/0.52  fof(f3098,plain,(
% 1.34/0.52    spl2_105 <=> ! [X10] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).
% 1.34/0.52  fof(f3103,plain,(
% 1.34/0.52    ( ! [X3] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X3)),X3),k1_xboole_0)) ) | (~spl2_11 | ~spl2_105)),
% 1.34/0.52    inference(resolution,[],[f3099,f104])).
% 1.34/0.52  fof(f104,plain,(
% 1.34/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl2_11),
% 1.34/0.52    inference(avatar_component_clause,[],[f103])).
% 1.34/0.52  fof(f3099,plain,(
% 1.34/0.52    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)) ) | ~spl2_105),
% 1.34/0.52    inference(avatar_component_clause,[],[f3098])).
% 1.34/0.52  fof(f3100,plain,(
% 1.34/0.52    spl2_105 | ~spl2_44 | ~spl2_67 | ~spl2_82 | ~spl2_104),
% 1.34/0.52    inference(avatar_split_clause,[],[f3096,f3058,f2023,f1444,f549,f3098])).
% 1.34/0.52  fof(f549,plain,(
% 1.34/0.52    spl2_44 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.34/0.52  fof(f1444,plain,(
% 1.34/0.52    spl2_67 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 1.34/0.52  fof(f2023,plain,(
% 1.34/0.52    spl2_82 <=> ! [X13,X14] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 1.34/0.52  fof(f3058,plain,(
% 1.34/0.52    spl2_104 <=> ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 1.34/0.52  fof(f3096,plain,(
% 1.34/0.52    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_xboole_0)) ) | (~spl2_44 | ~spl2_67 | ~spl2_82 | ~spl2_104)),
% 1.34/0.52    inference(forward_demodulation,[],[f3095,f1446])).
% 1.34/0.52  fof(f1446,plain,(
% 1.34/0.52    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_67),
% 1.34/0.52    inference(avatar_component_clause,[],[f1444])).
% 1.34/0.52  fof(f3095,plain,(
% 1.34/0.52    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl2_44 | ~spl2_82 | ~spl2_104)),
% 1.34/0.52    inference(subsumption_resolution,[],[f3078,f2024])).
% 1.34/0.52  fof(f2024,plain,(
% 1.34/0.52    ( ! [X14,X13] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1))) ) | ~spl2_82),
% 1.34/0.52    inference(avatar_component_clause,[],[f2023])).
% 1.34/0.52  fof(f3078,plain,(
% 1.34/0.52    ( ! [X10] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X10)),X10),k1_relat_1(sK1))) ) | (~spl2_44 | ~spl2_104)),
% 1.34/0.52    inference(superposition,[],[f550,f3059])).
% 1.34/0.52  fof(f3059,plain,(
% 1.34/0.52    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) ) | ~spl2_104),
% 1.34/0.52    inference(avatar_component_clause,[],[f3058])).
% 1.34/0.52  fof(f550,plain,(
% 1.34/0.52    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl2_44),
% 1.34/0.52    inference(avatar_component_clause,[],[f549])).
% 1.34/0.52  fof(f3060,plain,(
% 1.34/0.52    spl2_104 | ~spl2_32 | ~spl2_99),
% 1.34/0.52    inference(avatar_split_clause,[],[f2772,f2536,f263,f3058])).
% 1.34/0.52  fof(f263,plain,(
% 1.34/0.52    spl2_32 <=> ! [X1] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.34/0.52  fof(f2536,plain,(
% 1.34/0.52    spl2_99 <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 1.34/0.52  fof(f2772,plain,(
% 1.34/0.52    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) ) | (~spl2_32 | ~spl2_99)),
% 1.34/0.52    inference(superposition,[],[f2537,f264])).
% 1.34/0.52  fof(f264,plain,(
% 1.34/0.52    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)) ) | ~spl2_32),
% 1.34/0.52    inference(avatar_component_clause,[],[f263])).
% 1.34/0.52  fof(f2537,plain,(
% 1.34/0.52    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl2_99),
% 1.34/0.52    inference(avatar_component_clause,[],[f2536])).
% 1.34/0.52  fof(f2538,plain,(
% 1.34/0.52    spl2_99 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_76),
% 1.34/0.52    inference(avatar_split_clause,[],[f2144,f1862,f68,f63,f58,f2536])).
% 1.34/0.52  fof(f58,plain,(
% 1.34/0.52    spl2_1 <=> v1_relat_1(sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.34/0.52  fof(f63,plain,(
% 1.34/0.52    spl2_2 <=> v1_funct_1(sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.34/0.52  fof(f68,plain,(
% 1.34/0.52    spl2_3 <=> v2_funct_1(sK1)),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.34/0.52  fof(f1862,plain,(
% 1.34/0.52    spl2_76 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.34/0.52  fof(f2144,plain,(
% 1.34/0.52    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_76)),
% 1.34/0.52    inference(subsumption_resolution,[],[f2143,f60])).
% 1.34/0.52  fof(f60,plain,(
% 1.34/0.52    v1_relat_1(sK1) | ~spl2_1),
% 1.34/0.52    inference(avatar_component_clause,[],[f58])).
% 1.34/0.52  fof(f2143,plain,(
% 1.34/0.52    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_76)),
% 1.34/0.52    inference(subsumption_resolution,[],[f2142,f65])).
% 1.34/0.52  fof(f65,plain,(
% 1.34/0.52    v1_funct_1(sK1) | ~spl2_2),
% 1.34/0.52    inference(avatar_component_clause,[],[f63])).
% 1.34/0.52  fof(f2142,plain,(
% 1.34/0.52    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_76)),
% 1.34/0.52    inference(resolution,[],[f1863,f70])).
% 1.34/0.52  fof(f70,plain,(
% 1.34/0.52    v2_funct_1(sK1) | ~spl2_3),
% 1.34/0.52    inference(avatar_component_clause,[],[f68])).
% 1.34/0.52  fof(f1863,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl2_76),
% 1.34/0.52    inference(avatar_component_clause,[],[f1862])).
% 1.34/0.52  fof(f2025,plain,(
% 1.34/0.52    spl2_82 | ~spl2_36 | ~spl2_65),
% 1.34/0.52    inference(avatar_split_clause,[],[f1971,f1399,f311,f2023])).
% 1.34/0.52  fof(f311,plain,(
% 1.34/0.52    spl2_36 <=> ! [X9,X11,X10] : r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 1.34/0.52  fof(f1399,plain,(
% 1.34/0.52    spl2_65 <=> ! [X34] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))),
% 1.34/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 1.34/0.52  fof(f1971,plain,(
% 1.34/0.52    ( ! [X14,X13] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X13),X14),k1_relat_1(sK1))) ) | (~spl2_36 | ~spl2_65)),
% 1.34/0.52    inference(superposition,[],[f312,f1400])).
% 1.34/0.52  fof(f1400,plain,(
% 1.34/0.52    ( ! [X34] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))) ) | ~spl2_65),
% 1.34/0.52    inference(avatar_component_clause,[],[f1399])).
% 1.34/0.52  fof(f312,plain,(
% 1.34/0.52    ( ! [X10,X11,X9] : (r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11))) ) | ~spl2_36),
% 1.34/0.52    inference(avatar_component_clause,[],[f311])).
% 1.34/0.52  fof(f1864,plain,(
% 1.34/0.52    spl2_76),
% 1.34/0.52    inference(avatar_split_clause,[],[f50,f1862])).
% 1.34/0.52  fof(f50,plain,(
% 1.34/0.52    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.34/0.52    inference(cnf_transformation,[],[f29])).
% 1.34/0.52  fof(f29,plain,(
% 1.34/0.52    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.52    inference(flattening,[],[f28])).
% 1.34/0.52  fof(f28,plain,(
% 1.34/0.52    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.34/0.52    inference(ennf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.34/0.53  fof(f1447,plain,(
% 1.34/0.53    spl2_67 | ~spl2_15 | ~spl2_66),
% 1.34/0.53    inference(avatar_split_clause,[],[f1436,f1408,f125,f1444])).
% 1.34/0.53  fof(f125,plain,(
% 1.34/0.53    spl2_15 <=> ! [X3] : k1_xboole_0 = k6_subset_1(X3,X3)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.34/0.53  fof(f1408,plain,(
% 1.34/0.53    spl2_66 <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 1.34/0.53  fof(f1436,plain,(
% 1.34/0.53    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl2_15 | ~spl2_66)),
% 1.34/0.53    inference(forward_demodulation,[],[f1413,f126])).
% 1.34/0.53  fof(f126,plain,(
% 1.34/0.53    ( ! [X3] : (k1_xboole_0 = k6_subset_1(X3,X3)) ) | ~spl2_15),
% 1.34/0.53    inference(avatar_component_clause,[],[f125])).
% 1.34/0.53  fof(f1413,plain,(
% 1.34/0.53    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) ) | (~spl2_15 | ~spl2_66)),
% 1.34/0.53    inference(superposition,[],[f1409,f126])).
% 1.34/0.53  fof(f1409,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | ~spl2_66),
% 1.34/0.53    inference(avatar_component_clause,[],[f1408])).
% 1.34/0.53  fof(f1410,plain,(
% 1.34/0.53    spl2_66 | ~spl2_1 | ~spl2_2 | ~spl2_55),
% 1.34/0.53    inference(avatar_split_clause,[],[f1403,f771,f63,f58,f1408])).
% 1.34/0.53  fof(f771,plain,(
% 1.34/0.53    spl2_55 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 1.34/0.53  fof(f1403,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_55)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1402,f60])).
% 1.34/0.53  fof(f1402,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_55)),
% 1.34/0.53    inference(resolution,[],[f772,f65])).
% 1.34/0.53  fof(f772,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl2_55),
% 1.34/0.53    inference(avatar_component_clause,[],[f771])).
% 1.34/0.53  fof(f1401,plain,(
% 1.34/0.53    spl2_65 | ~spl2_28 | ~spl2_61),
% 1.34/0.53    inference(avatar_split_clause,[],[f1362,f1335,f235,f1399])).
% 1.34/0.53  fof(f235,plain,(
% 1.34/0.53    spl2_28 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.34/0.53  fof(f1335,plain,(
% 1.34/0.53    spl2_61 <=> ! [X5,X4] : (k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5 | k1_xboole_0 != k6_subset_1(X4,X5))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 1.34/0.53  fof(f1362,plain,(
% 1.34/0.53    ( ! [X34] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))) ) | (~spl2_28 | ~spl2_61)),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f1355])).
% 1.34/0.53  fof(f1355,plain,(
% 1.34/0.53    ( ! [X34] : (k1_xboole_0 != k1_xboole_0 | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X34),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X34)))) ) | (~spl2_28 | ~spl2_61)),
% 1.34/0.53    inference(superposition,[],[f1336,f236])).
% 1.34/0.53  fof(f236,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_28),
% 1.34/0.53    inference(avatar_component_clause,[],[f235])).
% 1.34/0.53  fof(f1336,plain,(
% 1.34/0.53    ( ! [X4,X5] : (k1_xboole_0 != k6_subset_1(X4,X5) | k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5) ) | ~spl2_61),
% 1.34/0.53    inference(avatar_component_clause,[],[f1335])).
% 1.34/0.53  fof(f1337,plain,(
% 1.34/0.53    spl2_61 | ~spl2_12 | ~spl2_22),
% 1.34/0.53    inference(avatar_split_clause,[],[f185,f175,f107,f1335])).
% 1.34/0.53  fof(f107,plain,(
% 1.34/0.53    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.34/0.53  fof(f175,plain,(
% 1.34/0.53    spl2_22 <=> ! [X1,X0] : (k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.34/0.53  fof(f185,plain,(
% 1.34/0.53    ( ! [X4,X5] : (k2_xboole_0(X4,k6_subset_1(X5,X4)) = X5 | k1_xboole_0 != k6_subset_1(X4,X5)) ) | (~spl2_12 | ~spl2_22)),
% 1.34/0.53    inference(resolution,[],[f176,f108])).
% 1.34/0.53  fof(f108,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) ) | ~spl2_12),
% 1.34/0.53    inference(avatar_component_clause,[],[f107])).
% 1.34/0.53  fof(f176,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1) ) | ~spl2_22),
% 1.34/0.53    inference(avatar_component_clause,[],[f175])).
% 1.34/0.53  fof(f773,plain,(
% 1.34/0.53    spl2_55),
% 1.34/0.53    inference(avatar_split_clause,[],[f49,f771])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.53    inference(flattening,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.34/0.53    inference(ennf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.34/0.53  fof(f551,plain,(
% 1.34/0.53    spl2_44 | ~spl2_1 | ~spl2_33),
% 1.34/0.53    inference(avatar_split_clause,[],[f547,f272,f58,f549])).
% 1.34/0.53  fof(f272,plain,(
% 1.34/0.53    spl2_33 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.34/0.53  fof(f547,plain,(
% 1.34/0.53    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_33)),
% 1.34/0.53    inference(resolution,[],[f273,f60])).
% 1.34/0.53  fof(f273,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl2_33),
% 1.34/0.53    inference(avatar_component_clause,[],[f272])).
% 1.34/0.53  fof(f313,plain,(
% 1.34/0.53    spl2_36 | ~spl2_17 | ~spl2_35),
% 1.34/0.53    inference(avatar_split_clause,[],[f298,f283,f143,f311])).
% 1.34/0.53  fof(f143,plain,(
% 1.34/0.53    spl2_17 <=> ! [X1,X0,X2] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.34/0.53  fof(f283,plain,(
% 1.34/0.53    spl2_35 <=> ! [X1,X2] : k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 1.34/0.53  fof(f298,plain,(
% 1.34/0.53    ( ! [X10,X11,X9] : (r1_tarski(k6_subset_1(X9,X10),k2_xboole_0(X9,X11))) ) | (~spl2_17 | ~spl2_35)),
% 1.34/0.53    inference(superposition,[],[f144,f284])).
% 1.34/0.53  fof(f284,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1) ) | ~spl2_35),
% 1.34/0.53    inference(avatar_component_clause,[],[f283])).
% 1.34/0.53  fof(f144,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ) | ~spl2_17),
% 1.34/0.53    inference(avatar_component_clause,[],[f143])).
% 1.34/0.53  fof(f285,plain,(
% 1.34/0.53    spl2_35 | ~spl2_6 | ~spl2_22),
% 1.34/0.53    inference(avatar_split_clause,[],[f183,f175,f81,f283])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    spl2_6 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.34/0.53  fof(f183,plain,(
% 1.34/0.53    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),k6_subset_1(X1,k6_subset_1(X1,X2))) = X1) ) | (~spl2_6 | ~spl2_22)),
% 1.34/0.53    inference(resolution,[],[f176,f82])).
% 1.34/0.53  fof(f82,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl2_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f81])).
% 1.34/0.53  fof(f274,plain,(
% 1.34/0.53    spl2_33),
% 1.34/0.53    inference(avatar_split_clause,[],[f42,f272])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(flattening,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.34/0.53  fof(f265,plain,(
% 1.34/0.53    spl2_32 | ~spl2_11 | ~spl2_31),
% 1.34/0.53    inference(avatar_split_clause,[],[f261,f257,f103,f263])).
% 1.34/0.53  fof(f257,plain,(
% 1.34/0.53    spl2_31 <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.34/0.53  fof(f261,plain,(
% 1.34/0.53    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X1)) ) | (~spl2_11 | ~spl2_31)),
% 1.34/0.53    inference(resolution,[],[f258,f104])).
% 1.34/0.53  fof(f258,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_31),
% 1.34/0.53    inference(avatar_component_clause,[],[f257])).
% 1.34/0.53  fof(f259,plain,(
% 1.34/0.53    spl2_31 | ~spl2_1 | ~spl2_2 | ~spl2_30),
% 1.34/0.53    inference(avatar_split_clause,[],[f255,f251,f63,f58,f257])).
% 1.34/0.53  fof(f251,plain,(
% 1.34/0.53    spl2_30 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.34/0.53  fof(f255,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_30)),
% 1.34/0.53    inference(subsumption_resolution,[],[f254,f60])).
% 1.34/0.53  fof(f254,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_30)),
% 1.34/0.53    inference(resolution,[],[f252,f65])).
% 1.34/0.53  fof(f252,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_30),
% 1.34/0.53    inference(avatar_component_clause,[],[f251])).
% 1.34/0.53  fof(f253,plain,(
% 1.34/0.53    spl2_30),
% 1.34/0.53    inference(avatar_split_clause,[],[f44,f251])).
% 1.34/0.53  fof(f44,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(flattening,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,axiom,(
% 1.34/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.34/0.53  fof(f237,plain,(
% 1.34/0.53    spl2_28 | ~spl2_1 | ~spl2_26),
% 1.34/0.53    inference(avatar_split_clause,[],[f233,f226,f58,f235])).
% 1.34/0.53  fof(f226,plain,(
% 1.34/0.53    spl2_26 <=> ! [X5,X4] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4)) | ~v1_relat_1(X4))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.34/0.53  fof(f233,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_26)),
% 1.34/0.53    inference(resolution,[],[f227,f60])).
% 1.34/0.53  fof(f227,plain,(
% 1.34/0.53    ( ! [X4,X5] : (~v1_relat_1(X4) | k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4))) ) | ~spl2_26),
% 1.34/0.53    inference(avatar_component_clause,[],[f226])).
% 1.34/0.53  fof(f228,plain,(
% 1.34/0.53    spl2_26 | ~spl2_9 | ~spl2_11),
% 1.34/0.53    inference(avatar_split_clause,[],[f114,f103,f95,f226])).
% 1.34/0.53  fof(f95,plain,(
% 1.34/0.53    spl2_9 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.34/0.53  fof(f114,plain,(
% 1.34/0.53    ( ! [X4,X5] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X4,X5),k1_relat_1(X4)) | ~v1_relat_1(X4)) ) | (~spl2_9 | ~spl2_11)),
% 1.34/0.53    inference(resolution,[],[f104,f96])).
% 1.34/0.53  fof(f96,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_9),
% 1.34/0.53    inference(avatar_component_clause,[],[f95])).
% 1.34/0.53  fof(f177,plain,(
% 1.34/0.53    spl2_22),
% 1.34/0.53    inference(avatar_split_clause,[],[f53,f175])).
% 1.34/0.53  fof(f53,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f43,f40])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,axiom,(
% 1.34/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.34/0.53  fof(f161,plain,(
% 1.34/0.53    ~spl2_19 | spl2_8 | ~spl2_12),
% 1.34/0.53    inference(avatar_split_clause,[],[f154,f107,f90,f158])).
% 1.34/0.53  fof(f90,plain,(
% 1.34/0.53    spl2_8 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.34/0.53  fof(f154,plain,(
% 1.34/0.53    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | (spl2_8 | ~spl2_12)),
% 1.34/0.53    inference(resolution,[],[f108,f92])).
% 1.34/0.53  fof(f92,plain,(
% 1.34/0.53    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_8),
% 1.34/0.53    inference(avatar_component_clause,[],[f90])).
% 1.34/0.53  fof(f145,plain,(
% 1.34/0.53    spl2_17 | ~spl2_10 | ~spl2_14),
% 1.34/0.53    inference(avatar_split_clause,[],[f128,f121,f99,f143])).
% 1.34/0.53  fof(f99,plain,(
% 1.34/0.53    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.34/0.53  fof(f121,plain,(
% 1.34/0.53    spl2_14 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.34/0.53  fof(f128,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ) | (~spl2_10 | ~spl2_14)),
% 1.34/0.53    inference(resolution,[],[f122,f100])).
% 1.34/0.53  fof(f100,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_10),
% 1.34/0.53    inference(avatar_component_clause,[],[f99])).
% 1.34/0.53  fof(f122,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_14),
% 1.34/0.53    inference(avatar_component_clause,[],[f121])).
% 1.34/0.53  fof(f127,plain,(
% 1.34/0.53    spl2_15 | ~spl2_7 | ~spl2_11),
% 1.34/0.53    inference(avatar_split_clause,[],[f113,f103,f86,f125])).
% 1.34/0.53  fof(f86,plain,(
% 1.34/0.53    spl2_7 <=> ! [X0] : r1_tarski(X0,X0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.34/0.53  fof(f113,plain,(
% 1.34/0.53    ( ! [X3] : (k1_xboole_0 = k6_subset_1(X3,X3)) ) | (~spl2_7 | ~spl2_11)),
% 1.34/0.53    inference(resolution,[],[f104,f87])).
% 1.34/0.53  fof(f87,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f86])).
% 1.34/0.53  fof(f123,plain,(
% 1.34/0.53    spl2_14 | ~spl2_7 | ~spl2_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f110,f99,f86,f121])).
% 1.34/0.53  fof(f110,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_7 | ~spl2_10)),
% 1.34/0.53    inference(resolution,[],[f100,f87])).
% 1.34/0.53  fof(f109,plain,(
% 1.34/0.53    spl2_12),
% 1.34/0.53    inference(avatar_split_clause,[],[f55,f107])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f45,f40])).
% 1.34/0.53  fof(f45,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.34/0.53    inference(nnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.53  fof(f105,plain,(
% 1.34/0.53    spl2_11),
% 1.34/0.53    inference(avatar_split_clause,[],[f54,f103])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f46,f40])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f32])).
% 1.34/0.53  fof(f101,plain,(
% 1.34/0.53    spl2_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f48,f99])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.34/0.53  fof(f97,plain,(
% 1.34/0.53    spl2_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f41,f95])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.34/0.53  fof(f93,plain,(
% 1.34/0.53    ~spl2_8),
% 1.34/0.53    inference(avatar_split_clause,[],[f36,f90])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.34/0.53    inference(flattening,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.34/0.53    inference(negated_conjecture,[],[f14])).
% 1.34/0.53  fof(f14,conjecture,(
% 1.34/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.34/0.53  fof(f88,plain,(
% 1.34/0.53    spl2_7 | ~spl2_5 | ~spl2_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f84,f81,f77,f86])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_5 | ~spl2_6)),
% 1.34/0.53    inference(superposition,[],[f82,f78])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    spl2_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f52,f81])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f39,f40])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.53  fof(f79,plain,(
% 1.34/0.53    spl2_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f51,f77])).
% 1.34/0.53  fof(f51,plain,(
% 1.34/0.53    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.34/0.53    inference(definition_unfolding,[],[f38,f40])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.34/0.53  fof(f71,plain,(
% 1.34/0.53    spl2_3),
% 1.34/0.53    inference(avatar_split_clause,[],[f35,f68])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    v2_funct_1(sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f66,plain,(
% 1.34/0.53    spl2_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f34,f63])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    v1_funct_1(sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    spl2_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f33,f58])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    v1_relat_1(sK1)),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (32608)------------------------------
% 1.34/0.53  % (32608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (32608)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (32608)Memory used [KB]: 8443
% 1.34/0.53  % (32608)Time elapsed: 0.091 s
% 1.34/0.53  % (32608)------------------------------
% 1.34/0.53  % (32608)------------------------------
% 1.34/0.53  % (32600)Success in time 0.171 s
%------------------------------------------------------------------------------
