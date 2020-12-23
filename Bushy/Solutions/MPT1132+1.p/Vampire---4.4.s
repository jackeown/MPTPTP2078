%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t63_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:46 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  360 (1064 expanded)
%              Number of leaves         :   71 ( 410 expanded)
%              Depth                    :   16
%              Number of atoms          : 1641 (4489 expanded)
%              Number of equality atoms :   33 ( 130 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f107,f114,f121,f128,f135,f142,f149,f156,f163,f170,f183,f184,f203,f268,f278,f299,f307,f359,f403,f451,f482,f489,f499,f503,f507,f509,f513,f523,f532,f553,f569,f647,f734,f767,f783,f830,f892,f996,f1037,f1045,f1052,f1201,f1375,f1390,f1476,f1513,f1520,f1799,f2164])).

fof(f2164,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | ~ spl7_48
    | spl7_51
    | ~ spl7_66
    | ~ spl7_68 ),
    inference(avatar_contradiction_clause,[],[f2163])).

fof(f2163,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_48
    | ~ spl7_51
    | ~ spl7_66
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f2162,f549])).

fof(f549,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl7_68
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f2162,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_48
    | ~ spl7_51
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f2160,f481])).

fof(f481,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl7_48
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f2160,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_51
    | ~ spl7_66 ),
    inference(resolution,[],[f1371,f488])).

fof(f488,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl7_51
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f1371,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1370,f106])).

fof(f106,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1370,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f1369,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1369,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(resolution,[],[f793,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t61_pre_topc)).

fof(f793,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f792,f106])).

fof(f792,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v2_pre_topc(sK1)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_4
    | ~ spl7_66 ),
    inference(subsumption_resolution,[],[f785,f113])).

fof(f785,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_66 ),
    inference(resolution,[],[f531,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0) )
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl7_66
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1799,plain,
    ( spl7_102
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f1711,f1518,f1797])).

fof(f1797,plain,
    ( spl7_102
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f1518,plain,
    ( spl7_100
  <=> sK4(sK0,sK1,sK2) = sK5(k1_zfmisc_1(sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f1711,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(sK4(sK0,sK1,sK2)))
    | ~ spl7_100 ),
    inference(superposition,[],[f85,f1519])).

fof(f1519,plain,
    ( sK4(sK0,sK1,sK2) = sK5(k1_zfmisc_1(sK4(sK0,sK1,sK2)))
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',existence_m1_subset_1)).

fof(f1520,plain,
    ( spl7_100
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f1501,f518,f1518])).

fof(f518,plain,
    ( spl7_62
  <=> v1_xboole_0(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1501,plain,
    ( sK4(sK0,sK1,sK2) = sK5(k1_zfmisc_1(sK4(sK0,sK1,sK2)))
    | ~ spl7_62 ),
    inference(resolution,[],[f1376,f519])).

fof(f519,plain,
    ( v1_xboole_0(sK4(sK0,sK1,sK2))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f518])).

fof(f1376,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK4(sK0,sK1,sK2) = sK5(k1_zfmisc_1(X0)) )
    | ~ spl7_62 ),
    inference(resolution,[],[f554,f802])).

fof(f802,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK4(sK0,sK1,sK2) = X0 )
    | ~ spl7_62 ),
    inference(resolution,[],[f519,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t8_boole)).

fof(f554,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f304,f85])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK5(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f193,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t2_subset)).

fof(f193,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK5(k1_zfmisc_1(X5)))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f81,f85])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t5_subset)).

fof(f1513,plain,
    ( spl7_98
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f579,f154,f1511])).

fof(f1511,plain,
    ( spl7_98
  <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f154,plain,
    ( spl7_16
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f579,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ spl7_16 ),
    inference(resolution,[],[f309,f155])).

fof(f155,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f309,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f308,f188])).

fof(f188,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f79,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',dt_g1_pre_topc)).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',dt_u1_pre_topc)).

fof(f308,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f189,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',abstractness_v1_pre_topc)).

fof(f189,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1476,plain,
    ( spl7_96
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1260,f1050,f294,f1474])).

fof(f1474,plain,
    ( spl7_96
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f294,plain,
    ( spl7_38
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f1050,plain,
    ( spl7_86
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f1260,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f1210,f295])).

fof(f295,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1210,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_86 ),
    inference(superposition,[],[f189,f1051])).

fof(f1051,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1390,plain,
    ( spl7_92
    | ~ spl7_95
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f791,f530,f1388,f1382])).

fof(f1382,plain,
    ( spl7_92
  <=> v4_pre_topc(k10_relat_1(sK2,sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1388,plain,
    ( spl7_95
  <=> ~ v4_pre_topc(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f791,plain,
    ( ~ v4_pre_topc(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(k10_relat_1(sK2,sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),sK0)
    | ~ spl7_66 ),
    inference(resolution,[],[f531,f85])).

fof(f1375,plain,
    ( ~ spl7_8
    | spl7_89 ),
    inference(avatar_contradiction_clause,[],[f1374])).

fof(f1374,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f1373,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1373,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_89 ),
    inference(resolution,[],[f1194,f188])).

fof(f1194,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1193,plain,
    ( spl7_89
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f1201,plain,
    ( ~ spl7_89
    | spl7_90
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f1061,f1043,f1199,f1193])).

fof(f1199,plain,
    ( spl7_90
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f1043,plain,
    ( spl7_84
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f1061,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_84 ),
    inference(superposition,[],[f189,f1044])).

fof(f1044,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1052,plain,
    ( spl7_86
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f578,f112,f1050])).

fof(f578,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_4 ),
    inference(resolution,[],[f309,f113])).

fof(f1045,plain,
    ( spl7_84
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f577,f126,f1043])).

fof(f577,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_8 ),
    inference(resolution,[],[f309,f127])).

fof(f1037,plain,
    ( spl7_22
    | spl7_82
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f773,f147,f140,f126,f112,f105,f98,f1035,f172])).

fof(f172,plain,
    ( spl7_22
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1035,plain,
    ( spl7_82
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f98,plain,
    ( spl7_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f140,plain,
    ( spl7_12
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f147,plain,
    ( spl7_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f773,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f772,f127])).

fof(f772,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f771,f106])).

fof(f771,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f770,f141])).

fof(f141,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f770,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f769,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f98])).

fof(f769,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f740,f113])).

fof(f740,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f350,f148])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f350,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(X9,sK4(X7,X6,X8))
      | m1_subset_1(X9,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X7)
      | v5_pre_topc(X8,X7,X6) ) ),
    inference(subsumption_resolution,[],[f346,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',d12_pre_topc)).

fof(f346,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ v2_pre_topc(X6)
      | ~ v4_pre_topc(sK4(X7,X6,X8),X6)
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(X9,sK4(X7,X6,X8))
      | m1_subset_1(X9,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
      | ~ l1_pre_topc(X7)
      | v5_pre_topc(X8,X7,X6) ) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ v2_pre_topc(X6)
      | ~ v4_pre_topc(sK4(X7,X6,X8),X6)
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(X9,sK4(X7,X6,X8))
      | m1_subset_1(X9,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X7),u1_struct_0(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
      | ~ l1_pre_topc(X7)
      | v5_pre_topc(X8,X7,X6) ) ),
    inference(resolution,[],[f220,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | m1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t4_subset)).

fof(f996,plain,
    ( ~ spl7_81
    | spl7_75
    | spl7_79 ),
    inference(avatar_split_clause,[],[f923,f890,f642,f994])).

fof(f994,plain,
    ( spl7_81
  <=> ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f642,plain,
    ( spl7_75
  <=> ~ v1_xboole_0(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f890,plain,
    ( spl7_79
  <=> ~ r2_hidden(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f923,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1))
    | ~ spl7_75
    | ~ spl7_79 ),
    inference(subsumption_resolution,[],[f922,f643])).

fof(f643,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f642])).

fof(f922,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1))
    | ~ spl7_79 ),
    inference(resolution,[],[f891,f83])).

fof(f891,plain,
    ( ~ r2_hidden(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1))
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f890])).

fof(f892,plain,
    ( ~ spl7_79
    | ~ spl7_4
    | spl7_77 ),
    inference(avatar_split_clause,[],[f768,f732,f112,f890])).

fof(f732,plain,
    ( spl7_77
  <=> ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f768,plain,
    ( ~ r2_hidden(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1))
    | ~ spl7_4
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f759,f113])).

fof(f759,plain,
    ( ~ r2_hidden(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_77 ),
    inference(resolution,[],[f733,f206])).

fof(f206,plain,(
    ! [X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(X2,u1_pre_topc(X3))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f82,f79])).

fof(f733,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f732])).

fof(f830,plain,
    ( spl7_24
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_77 ),
    inference(avatar_split_clause,[],[f781,f732,f168,f161,f126,f112,f105,f98,f178])).

fof(f178,plain,
    ( spl7_24
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f161,plain,
    ( spl7_18
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f168,plain,
    ( spl7_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f781,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f780,f99])).

fof(f780,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f779,f106])).

fof(f779,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f762,f113])).

fof(f762,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f761,f127])).

fof(f761,plain,
    ( ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f760,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f760,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_18
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f758,f162])).

fof(f162,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f758,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_77 ),
    inference(resolution,[],[f733,f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f244,f188])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f240,f67])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f783,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | spl7_23
    | spl7_69 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_23
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f176,f778])).

fof(f778,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f777,f127])).

fof(f777,plain,
    ( ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f776,f148])).

fof(f776,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f775,f141])).

fof(f775,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f774,f99])).

fof(f774,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f558,f113])).

fof(f558,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_69 ),
    inference(resolution,[],[f552,f66])).

fof(f552,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl7_69
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f176,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_23
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f767,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25
    | spl7_77 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f765,f99])).

fof(f765,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f764,f106])).

fof(f764,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f763,f113])).

fof(f763,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f762,f182])).

fof(f182,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_25
  <=> ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f734,plain,
    ( ~ spl7_77
    | spl7_41
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f526,f505,f449,f357,f732])).

fof(f357,plain,
    ( spl7_41
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f449,plain,
    ( spl7_46
  <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f505,plain,
    ( spl7_58
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f526,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_41
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f524,f450])).

fof(f450,plain,
    ( v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f449])).

fof(f524,plain,
    ( ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_41
    | ~ spl7_58 ),
    inference(resolution,[],[f506,f358])).

fof(f358,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f357])).

fof(f506,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f505])).

fof(f647,plain,
    ( ~ spl7_73
    | spl7_74
    | spl7_71 ),
    inference(avatar_split_clause,[],[f583,f567,f645,f639])).

fof(f639,plain,
    ( spl7_73
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f645,plain,
    ( spl7_74
  <=> v1_xboole_0(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f567,plain,
    ( spl7_71
  <=> ~ r2_hidden(sK4(sK0,sK1,sK2),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f583,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_pre_topc(sK1))
    | ~ spl7_71 ),
    inference(resolution,[],[f568,f83])).

fof(f568,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2),u1_pre_topc(sK1))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f567])).

fof(f569,plain,
    ( ~ spl7_71
    | ~ spl7_4
    | spl7_69 ),
    inference(avatar_split_clause,[],[f560,f551,f112,f567])).

fof(f560,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2),u1_pre_topc(sK1))
    | ~ spl7_4
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f559,f113])).

fof(f559,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_69 ),
    inference(resolution,[],[f552,f206])).

fof(f553,plain,
    ( ~ spl7_69
    | ~ spl7_48
    | spl7_51
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f527,f505,f487,f480,f551])).

fof(f527,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_48
    | ~ spl7_51
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f525,f481])).

fof(f525,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_51
    | ~ spl7_58 ),
    inference(resolution,[],[f506,f488])).

fof(f532,plain,
    ( ~ spl7_25
    | spl7_66
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f475,f294,f168,f161,f126,f98,f530,f181])).

fof(f475,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f474,f127])).

fof(f474,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f473,f169])).

fof(f473,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f472,f162])).

fof(f472,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_0
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f471,f99])).

fof(f471,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f280,f295])).

fof(f280,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl7_20 ),
    inference(superposition,[],[f65,f217])).

fof(f217,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl7_20 ),
    inference(resolution,[],[f86,f169])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',redefinition_k8_relset_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f523,plain,
    ( spl7_62
    | spl7_64
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f508,f501,f521,f518])).

fof(f521,plain,
    ( spl7_64
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,sK4(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f501,plain,
    ( spl7_56
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f508,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | v1_xboole_0(sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,sK4(sK0,sK1,sK2)) )
    | ~ spl7_56 ),
    inference(resolution,[],[f502,f83])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f501])).

fof(f513,plain,
    ( spl7_60
    | spl7_24
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f384,f294,f168,f161,f126,f98,f178,f511])).

fof(f511,plain,
    ( spl7_60
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f384,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f383,f127])).

fof(f383,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f382,f295])).

fof(f382,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f381,f162])).

fof(f381,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f378,f99])).

fof(f378,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | m1_subset_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_20 ),
    inference(resolution,[],[f242,f169])).

fof(f242,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X8),u1_struct_0(X6))
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(X8)
      | v5_pre_topc(X7,X8,X6)
      | ~ r2_hidden(X9,sK4(X8,X6,X7))
      | m1_subset_1(X9,u1_struct_0(X6)) ) ),
    inference(resolution,[],[f66,f82])).

fof(f509,plain,
    ( spl7_46
    | spl7_24
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f470,f168,f161,f126,f112,f105,f98,f178,f449])).

fof(f470,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f469,f106])).

fof(f469,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f417,f113])).

fof(f417,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f416,f127])).

fof(f416,plain,
    ( ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f415,f99])).

fof(f415,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f412,f162])).

fof(f412,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_20 ),
    inference(resolution,[],[f247,f169])).

fof(f247,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),X3) ) ),
    inference(subsumption_resolution,[],[f246,f188])).

fof(f246,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),X3) ) ),
    inference(subsumption_resolution,[],[f241,f67])).

fof(f241,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v2_pre_topc(X3)
      | v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),X3) ) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f507,plain,
    ( ~ spl7_23
    | spl7_58
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f260,f147,f140,f126,f112,f98,f505,f175])).

fof(f260,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f259,f127])).

fof(f259,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f258,f148])).

fof(f258,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f257,f141])).

fof(f257,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f256,f99])).

fof(f256,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f254,f113])).

fof(f254,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl7_14 ),
    inference(superposition,[],[f65,f216])).

fof(f216,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl7_14 ),
    inference(resolution,[],[f86,f148])).

fof(f503,plain,
    ( spl7_56
    | spl7_22
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f455,f147,f140,f126,f112,f98,f172,f501])).

fof(f455,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f454,f127])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f453,f113])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f452,f141])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f377,f99])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f242,f148])).

fof(f499,plain,
    ( ~ spl7_53
    | spl7_54
    | spl7_22
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f459,f147,f140,f126,f112,f98,f172,f497,f494])).

fof(f494,plain,
    ( spl7_53
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f497,plain,
    ( spl7_54
  <=> ! [X0] : ~ r2_hidden(X0,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f459,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f458,f127])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f457,f113])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f456,f141])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_0
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f368,f99])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,sK1)
        | ~ r2_hidden(X0,sK4(sK0,sK1,sK2))
        | ~ v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f243,f148])).

fof(f243,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X10))))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X12),u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(X12)
      | v5_pre_topc(X11,X12,X10)
      | ~ r2_hidden(X13,sK4(X12,X10,X11))
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(resolution,[],[f66,f81])).

fof(f489,plain,
    ( spl7_22
    | ~ spl7_51
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f464,f147,f140,f126,f112,f98,f487,f172])).

fof(f464,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f463,f127])).

fof(f463,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f462,f148])).

fof(f462,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f461,f141])).

fof(f461,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f460,f99])).

fof(f460,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f251,f113])).

fof(f251,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(superposition,[],[f68,f216])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f482,plain,
    ( spl7_22
    | spl7_48
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f468,f147,f140,f126,f112,f98,f480,f172])).

fof(f468,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f467,f127])).

fof(f467,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f466,f141])).

fof(f466,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f465,f99])).

fof(f465,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f232,f113])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f67,f148])).

fof(f451,plain,
    ( spl7_46
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f420,f181,f168,f161,f126,f112,f105,f98,f449])).

fof(f420,plain,
    ( v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f419,f106])).

fof(f419,plain,
    ( ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f418,f113])).

fof(f418,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f417,f182])).

fof(f403,plain,
    ( ~ spl7_43
    | spl7_44
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f376,f294,f181,f168,f161,f126,f98,f401,f398])).

fof(f398,plain,
    ( spl7_43
  <=> ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f401,plain,
    ( spl7_44
  <=> ! [X1] : ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f376,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f375,f182])).

fof(f375,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f374,f127])).

fof(f374,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f373,f295])).

fof(f373,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f372,f162])).

fof(f372,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f369,f99])).

fof(f369,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ r2_hidden(X1,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2))
        | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )
    | ~ spl7_20 ),
    inference(resolution,[],[f243,f169])).

fof(f359,plain,
    ( ~ spl7_39
    | ~ spl7_41
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f286,f181,f168,f161,f126,f98,f357,f297])).

fof(f297,plain,
    ( spl7_39
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f286,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f285,f182])).

fof(f285,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f284,f127])).

fof(f284,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f283,f169])).

fof(f283,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f282,f162])).

fof(f282,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f279,f99])).

fof(f279,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_20 ),
    inference(superposition,[],[f68,f217])).

fof(f307,plain,
    ( ~ spl7_4
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f305,f113])).

fof(f305,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl7_39 ),
    inference(resolution,[],[f188,f298])).

fof(f298,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl7_36
    | ~ spl7_39
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | spl7_25 ),
    inference(avatar_split_clause,[],[f239,f181,f168,f161,f126,f98,f297,f291])).

fof(f291,plain,
    ( spl7_36
  <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f239,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f238,f182])).

fof(f238,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f237,f127])).

fof(f237,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f236,f162])).

fof(f236,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_0
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f233,f99])).

fof(f233,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_20 ),
    inference(resolution,[],[f67,f169])).

fof(f278,plain,
    ( ~ spl7_33
    | spl7_34
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f249,f147,f276,f273])).

fof(f273,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f276,plain,
    ( spl7_34
  <=> ! [X3,X2] : ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f249,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f227,f81])).

fof(f227,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f226,f148])).

fof(f226,plain,
    ( ! [X0] :
        ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f80,f216])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',dt_k8_relset_1)).

fof(f268,plain,
    ( ~ spl7_31
    | spl7_28
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f191,f168,f201,f266])).

fof(f266,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f201,plain,
    ( spl7_28
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) )
    | ~ spl7_20 ),
    inference(resolution,[],[f81,f169])).

fof(f203,plain,
    ( ~ spl7_27
    | spl7_28
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f190,f147,f201,f198])).

fof(f198,plain,
    ( spl7_27
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f81,f148])).

fof(f184,plain,
    ( spl7_22
    | spl7_24 ),
    inference(avatar_split_clause,[],[f93,f178,f172])).

fof(f93,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f52,f57])).

fof(f57,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',t63_pre_topc)).

fof(f52,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f183,plain,
    ( ~ spl7_23
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f92,f181,f175])).

fof(f92,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f53,f57])).

fof(f53,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f170,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f89,f168])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f32])).

fof(f163,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f90,f161])).

fof(f90,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f55,f57])).

fof(f55,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f156,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f87,f154])).

fof(f87,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t63_pre_topc.p',existence_l1_pre_topc)).

fof(f149,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f60,f147])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f59,f140])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f135,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f57,f133])).

fof(f133,plain,
    ( spl7_10
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f128,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f64,f126])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f119,plain,
    ( spl7_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f62,f112])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f58,f98])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
