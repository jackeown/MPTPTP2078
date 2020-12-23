%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t52_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 45.79s
% Output     : Refutation 45.79s
% Verified   : 
% Statistics : Number of formulae       :  607 (2727 expanded)
%              Number of leaves         :   84 ( 970 expanded)
%              Depth                    :   30
%              Number of atoms          : 4017 (12526 expanded)
%              Number of equality atoms :  313 (1247 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f215,f222,f229,f236,f273,f280,f287,f300,f313,f321,f322,f367,f375,f384,f404,f407,f459,f462,f476,f490,f500,f505,f570,f580,f585,f594,f606,f614,f621,f992,f1130,f1189,f1704,f1783,f1896,f1927,f1951,f5799,f6204,f6519,f6990,f7873,f10160,f10525,f10659,f18262,f178015,f178638,f179187,f179498])).

fof(f179498,plain,
    ( spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_82
    | spl13_85
    | ~ spl13_1424 ),
    inference(avatar_contradiction_clause,[],[f179497])).

fof(f179497,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_1424 ),
    inference(subsumption_resolution,[],[f179496,f279])).

fof(f279,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl13_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f179496,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_1424 ),
    inference(subsumption_resolution,[],[f179495,f977])).

fof(f977,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl13_82
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f179495,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_85
    | ~ spl13_1424 ),
    inference(subsumption_resolution,[],[f179231,f983])).

fof(f983,plain,
    ( k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_85 ),
    inference(avatar_component_clause,[],[f982])).

fof(f982,plain,
    ( spl13_85
  <=> k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_85])])).

fof(f179231,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_1424 ),
    inference(superposition,[],[f670,f179186])).

fof(f179186,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = sK1
    | ~ spl13_1424 ),
    inference(avatar_component_clause,[],[f179185])).

fof(f179185,plain,
    ( spl13_1424
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1424])])).

fof(f670,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,k4_lattices(sK0,X3,X2),X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(duplicate_literal_removal,[],[f661])).

fof(f661,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,k4_lattices(sK0,X3,X2),X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(superposition,[],[f415,f408])).

fof(f408,plain,
    ( ! [X10,X11] :
        ( k4_lattices(sK0,X10,X11) = k4_lattices(sK0,X11,X10)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f388,f400])).

fof(f400,plain,
    ( l1_lattices(sK0)
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl13_32
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f388,plain,
    ( ! [X10,X11] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | k4_lattices(sK0,X10,X11) = k4_lattices(sK0,X11,X10) )
    | ~ spl13_1
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f242,f358])).

fof(f358,plain,
    ( v6_lattices(sK0)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl13_28
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f242,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | k4_lattices(sK0,X10,X11) = k4_lattices(sK0,X11,X10) )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f115])).

fof(f115,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',commutativity_k4_lattices)).

fof(f214,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,X0,X1),X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,X0,X1),X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(superposition,[],[f379,f397])).

fof(f397,plain,
    ( ! [X12,X13] :
        ( k4_lattices(sK0,X12,X13) = k2_lattices(sK0,X12,X13)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0)) )
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl13_30
  <=> ! [X13,X12] :
        ( ~ m1_subset_1(X12,u1_struct_0(sK0))
        | k4_lattices(sK0,X12,X13) = k2_lattices(sK0,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f379,plain,
    ( ! [X8,X9] :
        ( k1_lattices(sK0,k2_lattices(sK0,X8,X9),X9) = X9
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f263,f352])).

fof(f352,plain,
    ( v8_lattices(sK0)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl13_26
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f263,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X8,X9),X9) = X9
        | ~ v8_lattices(sK0) )
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f249,f214])).

fof(f249,plain,
    ( ! [X8,X9] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X8,X9),X9) = X9
        | ~ v8_lattices(sK0) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',d8_lattices)).

fof(f235,plain,
    ( l3_lattices(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl13_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f179187,plain,
    ( spl13_1424
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_42
    | ~ spl13_318
    | ~ spl13_1420 ),
    inference(avatar_split_clause,[],[f178751,f178636,f10657,f492,f271,f234,f227,f220,f213,f179185])).

fof(f220,plain,
    ( spl13_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f227,plain,
    ( spl13_4
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f271,plain,
    ( spl13_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f492,plain,
    ( spl13_42
  <=> ! [X9,X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k3_lattices(sK0,X8,X9) = k3_lattices(sK0,X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f10657,plain,
    ( spl13_318
  <=> k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_318])])).

fof(f178636,plain,
    ( spl13_1420
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1420])])).

fof(f178751,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_42
    | ~ spl13_318
    | ~ spl13_1420 ),
    inference(forward_demodulation,[],[f178750,f10658])).

fof(f10658,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ spl13_318 ),
    inference(avatar_component_clause,[],[f10657])).

fof(f178750,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_42
    | ~ spl13_1420 ),
    inference(subsumption_resolution,[],[f178688,f272])).

fof(f272,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f271])).

fof(f178688,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42
    | ~ spl13_1420 ),
    inference(superposition,[],[f178637,f706])).

fof(f706,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f705,f214])).

fof(f705,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f704,f235])).

fof(f704,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(duplicate_literal_removal,[],[f702])).

fof(f702,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(resolution,[],[f527,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',dt_k7_lattices)).

fof(f527,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,k7_lattices(sK0,X0)) = k6_lattices(sK0)
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_42 ),
    inference(superposition,[],[f493,f258])).

fof(f258,plain,
    ( ! [X3] :
        ( k3_lattices(sK0,k7_lattices(sK0,X3),X3) = k6_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f257,f214])).

fof(f257,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k7_lattices(sK0,X3),X3) = k6_lattices(sK0) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f256,f228])).

fof(f228,plain,
    ( v17_lattices(sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f227])).

fof(f256,plain,
    ( ! [X3] :
        ( ~ v17_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k7_lattices(sK0,X3),X3) = k6_lattices(sK0) )
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f246,f221])).

fof(f221,plain,
    ( v10_lattices(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f220])).

fof(f246,plain,
    ( ! [X3] :
        ( ~ v10_lattices(sK0)
        | ~ v17_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,k7_lattices(sK0,X3),X3) = k6_lattices(sK0) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t48_lattices)).

fof(f493,plain,
    ( ! [X8,X9] :
        ( k3_lattices(sK0,X8,X9) = k3_lattices(sK0,X9,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f492])).

fof(f178637,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ spl13_1420 ),
    inference(avatar_component_clause,[],[f178636])).

fof(f178638,plain,
    ( spl13_1420
    | spl13_1
    | ~ spl13_8
    | ~ spl13_36
    | ~ spl13_44
    | ~ spl13_82
    | ~ spl13_1416 ),
    inference(avatar_split_clause,[],[f178087,f178013,f976,f495,f454,f271,f213,f178636])).

fof(f454,plain,
    ( spl13_36
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f495,plain,
    ( spl13_44
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f178013,plain,
    ( spl13_1416
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1416])])).

fof(f178087,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_36
    | ~ spl13_44
    | ~ spl13_82
    | ~ spl13_1416 ),
    inference(subsumption_resolution,[],[f178086,f272])).

fof(f178086,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_36
    | ~ spl13_44
    | ~ spl13_82
    | ~ spl13_1416 ),
    inference(subsumption_resolution,[],[f178024,f977])).

fof(f178024,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_36
    | ~ spl13_44
    | ~ spl13_1416 ),
    inference(superposition,[],[f178014,f506])).

fof(f506,plain,
    ( ! [X6,X7] :
        ( k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(subsumption_resolution,[],[f464,f496])).

fof(f496,plain,
    ( v4_lattices(sK0)
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f495])).

fof(f464,plain,
    ( ! [X6,X7] :
        ( ~ v4_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7) )
    | ~ spl13_1
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f240,f455])).

fof(f455,plain,
    ( l2_lattices(sK0)
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f454])).

fof(f240,plain,
    ( ! [X6,X7] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7) )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',redefinition_k3_lattices)).

fof(f178014,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ spl13_1416 ),
    inference(avatar_component_clause,[],[f178013])).

fof(f178015,plain,
    ( spl13_1416
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(avatar_split_clause,[],[f177692,f18260,f10523,f6959,f1187,f976,f619,f604,f568,f495,f492,f474,f454,f399,f396,f357,f351,f319,f305,f298,f278,f271,f234,f220,f213,f178013])).

fof(f298,plain,
    ( spl13_14
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f305,plain,
    ( spl13_16
  <=> k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f319,plain,
    ( spl13_20
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f474,plain,
    ( spl13_40
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f568,plain,
    ( spl13_48
  <=> k7_lattices(sK0,k5_lattices(sK0)) = k6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f604,plain,
    ( spl13_56
  <=> ! [X5,X7,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X5,X6),k2_lattices(sK0,X5,X7)) = k2_lattices(sK0,X5,k1_lattices(sK0,X6,X7))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f619,plain,
    ( spl13_58
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f1187,plain,
    ( spl13_94
  <=> k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f6959,plain,
    ( spl13_212
  <=> m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_212])])).

fof(f10523,plain,
    ( spl13_314
  <=> k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_314])])).

fof(f18260,plain,
    ( spl13_472
  <=> k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k6_lattices(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_472])])).

fof(f177692,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f84786,f173216])).

fof(f173216,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k7_lattices(sK0,sK2)))
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_82 ),
    inference(resolution,[],[f167146,f977])).

fof(f167146,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f167145,f272])).

fof(f167145,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f149838,f279])).

fof(f149838,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f634,f306])).

fof(f306,plain,
    ( k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f305])).

fof(f634,plain,
    ( ! [X2,X0,X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,X0,X1),k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f622])).

fof(f622,plain,
    ( ! [X2,X0,X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,X0,X1),k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f605,f397])).

fof(f605,plain,
    ( ! [X6,X7,X5] :
        ( k1_lattices(sK0,k2_lattices(sK0,X5,X6),k2_lattices(sK0,X5,X7)) = k2_lattices(sK0,X5,k1_lattices(sK0,X6,X7))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f604])).

fof(f84786,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f84387,f19597])).

fof(f19597,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314 ),
    inference(backward_demodulation,[],[f19593,f17425])).

fof(f17425,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(backward_demodulation,[],[f17394,f17249])).

fof(f17249,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k7_lattices(sK0,sK2)))
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(resolution,[],[f7000,f977])).

fof(f7000,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X2)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X2)) )
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(subsumption_resolution,[],[f2058,f6960])).

fof(f6960,plain,
    ( m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0))
    | ~ spl13_212 ),
    inference(avatar_component_clause,[],[f6959])).

fof(f2058,plain,
    ( ! [X2] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X2)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(subsumption_resolution,[],[f2019,f279])).

fof(f2019,plain,
    ( ! [X2] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X2)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(superposition,[],[f605,f1188])).

fof(f1188,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2))
    | ~ spl13_94 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f17394,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k7_lattices(sK0,sK2)))
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(resolution,[],[f7002,f977])).

fof(f7002,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X5)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X5)) )
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(subsumption_resolution,[],[f2060,f6960])).

fof(f2060,plain,
    ( ! [X5] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X5)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(subsumption_resolution,[],[f2023,f279])).

fof(f2023,plain,
    ( ! [X5] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X5)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X5))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(superposition,[],[f633,f1188])).

fof(f633,plain,
    ( ! [X2,X0,X1] :
        ( k1_lattices(sK0,k2_lattices(sK0,X0,X2),k4_lattices(sK0,X0,X1)) = k2_lattices(sK0,X0,k1_lattices(sK0,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f623])).

fof(f623,plain,
    ( ! [X2,X0,X1] :
        ( k1_lattices(sK0,k2_lattices(sK0,X0,X2),k4_lattices(sK0,X0,X1)) = k2_lattices(sK0,X0,k1_lattices(sK0,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f605,f397])).

fof(f19593,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314 ),
    inference(backward_demodulation,[],[f19592,f17560])).

fof(f17560,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(forward_demodulation,[],[f17532,f17394])).

fof(f17532,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k7_lattices(sK0,sK2)))
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(resolution,[],[f7007,f977])).

fof(f7007,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,X16,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X16)) )
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(subsumption_resolution,[],[f2065,f6960])).

fof(f2065,plain,
    ( ! [X16] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,X16,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X16))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(subsumption_resolution,[],[f2036,f279])).

fof(f2036,plain,
    ( ! [X16] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,X16,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),X16))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_94 ),
    inference(superposition,[],[f818,f1188])).

fof(f818,plain,
    ( ! [X6,X4,X5] :
        ( k1_lattices(sK0,k2_lattices(sK0,X4,X6),k4_lattices(sK0,X5,X4)) = k2_lattices(sK0,X4,k1_lattices(sK0,X6,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,
    ( ! [X6,X4,X5] :
        ( k1_lattices(sK0,k2_lattices(sK0,X4,X6),k4_lattices(sK0,X5,X4)) = k2_lattices(sK0,X4,k1_lattices(sK0,X6,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(superposition,[],[f633,f408])).

fof(f19592,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_56
    | ~ spl13_82
    | ~ spl13_314 ),
    inference(forward_demodulation,[],[f19569,f10524])).

fof(f10524,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl13_314 ),
    inference(avatar_component_clause,[],[f10523])).

fof(f19569,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_56
    | ~ spl13_82 ),
    inference(resolution,[],[f15640,f279])).

fof(f15640,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK2),X4)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k5_lattices(sK0),X4)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_56
    | ~ spl13_82 ),
    inference(backward_demodulation,[],[f15532,f3337])).

fof(f3337,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)),k4_lattices(sK0,k7_lattices(sK0,sK2),X4)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k5_lattices(sK0),X4)) )
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56
    | ~ spl13_82 ),
    inference(resolution,[],[f1451,f977])).

fof(f1451,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k1_lattices(sK0,k4_lattices(sK0,X4,k5_lattices(sK0)),k4_lattices(sK0,X4,X5)) = k2_lattices(sK0,X4,k1_lattices(sK0,k5_lattices(sK0),X5)) )
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(resolution,[],[f821,f475])).

fof(f475,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f474])).

fof(f821,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,k4_lattices(sK0,X0,X1),k4_lattices(sK0,X0,X2)) = k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f803])).

fof(f803,plain,
    ( ! [X2,X0,X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,X0,X1),k4_lattices(sK0,X0,X2)) = k2_lattices(sK0,X0,k1_lattices(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f633,f397])).

fof(f15532,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) = k5_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_82 ),
    inference(resolution,[],[f9677,f977])).

fof(f9677,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,k5_lattices(sK0)) = k5_lattices(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(subsumption_resolution,[],[f9676,f475])).

fof(f9676,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,k5_lattices(sK0)) = k5_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(duplicate_literal_removal,[],[f9664])).

fof(f9664,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,k5_lattices(sK0)) = k5_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(resolution,[],[f1088,f421])).

fof(f421,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f420,f214])).

fof(f420,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f414,f400])).

fof(f414,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_30 ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_30 ),
    inference(superposition,[],[f198,f397])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',dt_k2_lattices)).

fof(f1088,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(k4_lattices(sK0,X6,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k4_lattices(sK0,X6,k5_lattices(sK0)) = k5_lattices(sK0) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(subsumption_resolution,[],[f1069,f475])).

fof(f1069,plain,
    ( ! [X6] :
        ( k4_lattices(sK0,X6,k5_lattices(sK0)) = k5_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X6,k5_lattices(sK0)),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(superposition,[],[f674,f528])).

fof(f528,plain,
    ( ! [X1] :
        ( k3_lattices(sK0,X1,k5_lattices(sK0)) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f526,f475])).

fof(f526,plain,
    ( ! [X1] :
        ( k3_lattices(sK0,X1,k5_lattices(sK0)) = X1
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_42 ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,
    ( ! [X1] :
        ( k3_lattices(sK0,X1,k5_lattices(sK0)) = X1
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_42 ),
    inference(superposition,[],[f493,f327])).

fof(f327,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f326,f235])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X0) = X0 )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f325,f214])).

fof(f325,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X0) = X0 )
    | ~ spl13_2
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f323,f221])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X0) = X0 )
    | ~ spl13_14 ),
    inference(resolution,[],[f299,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t39_lattices)).

fof(f299,plain,
    ( v13_lattices(sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f298])).

fof(f674,plain,
    ( ! [X2,X3] :
        ( k3_lattices(sK0,k4_lattices(sK0,X2,X3),X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(subsumption_resolution,[],[f668,f421])).

fof(f668,plain,
    ( ! [X2,X3] :
        ( k3_lattices(sK0,k4_lattices(sK0,X2,X3),X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(duplicate_literal_removal,[],[f663])).

fof(f663,plain,
    ( ! [X2,X3] :
        ( k3_lattices(sK0,k4_lattices(sK0,X2,X3),X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X2,X3),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(superposition,[],[f415,f506])).

fof(f84387,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_82
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(resolution,[],[f19346,f977])).

fof(f19346,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k2_lattices(sK0,X0,sK1) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f19329,f14815])).

fof(f14815,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k2_lattices(sK0,X0,k1_lattices(sK0,sK1,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f14814,f279])).

fof(f14814,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k2_lattices(sK0,X0,k1_lattices(sK0,sK1,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(duplicate_literal_removal,[],[f14802])).

fof(f14802,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k2_lattices(sK0,X0,k1_lattices(sK0,sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f3130,f421])).

fof(f3130,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k4_lattices(sK0,X2,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k4_lattices(sK0,X2,sK1) = k2_lattices(sK0,X2,k1_lattices(sK0,sK1,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f3109,f279])).

fof(f3109,plain,
    ( ! [X2] :
        ( k4_lattices(sK0,X2,sK1) = k2_lattices(sK0,X2,k1_lattices(sK0,sK1,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X2,sK1),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(superposition,[],[f1455,f673])).

fof(f673,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,X1,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f671,f620])).

fof(f620,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f619])).

fof(f671,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,X1,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(duplicate_literal_removal,[],[f660])).

fof(f660,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,X1,X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(superposition,[],[f415,f334])).

fof(f334,plain,
    ( ! [X0] :
        ( k4_lattices(sK0,k6_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f333,f235])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f332,f214])).

fof(f332,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 )
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f331,f221])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 )
    | ~ spl13_20 ),
    inference(resolution,[],[f320,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t43_lattices)).

fof(f320,plain,
    ( v14_lattices(sK0)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1455,plain,
    ( ! [X14,X15] :
        ( k1_lattices(sK0,k4_lattices(sK0,X14,sK1),k4_lattices(sK0,X14,X15)) = k2_lattices(sK0,X14,k1_lattices(sK0,sK1,X15))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(resolution,[],[f821,f279])).

fof(f19329,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f19293,f19269])).

fof(f19269,plain,
    ( k1_lattices(sK0,sK1,sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f19267,f11825])).

fof(f11825,plain,
    ( k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f3127,f279])).

fof(f3127,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),X1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f3126,f279])).

fof(f3126,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),X1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f3097,f620])).

fof(f3097,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),X1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f1455,f334])).

fof(f19267,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(forward_demodulation,[],[f19248,f18261])).

fof(f18261,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k6_lattices(sK0),sK1)) = sK1
    | ~ spl13_472 ),
    inference(avatar_component_clause,[],[f18260])).

fof(f19248,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314 ),
    inference(backward_demodulation,[],[f19229,f11523])).

fof(f11523,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314 ),
    inference(forward_demodulation,[],[f11494,f10524])).

fof(f11494,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f2718,f475])).

fof(f2718,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,X9,k2_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X9,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f860,f279])).

fof(f860,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,k2_lattices(sK0,k6_lattices(sK0),X3)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f858,f620])).

fof(f858,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,X2,k2_lattices(sK0,k6_lattices(sK0),X3)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X2,X3))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f842])).

fof(f842,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,X2,k2_lattices(sK0,k6_lattices(sK0),X3)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X2,X3))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f634,f334])).

fof(f19229,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f19228,f19019])).

fof(f19019,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f19018,f11852])).

fof(f11852,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) = k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f11851,f11533])).

fof(f11533,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) = k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f11505,f11411])).

fof(f11411,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f2691,f279])).

fof(f2691,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),X9),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X9,sK1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f822,f279])).

fof(f822,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),X3),X2) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X3,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f819,f620])).

fof(f819,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),X3),X2) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X3,X2))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f805])).

fof(f805,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),X3),X2) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,X3,X2))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f633,f334])).

fof(f11505,plain,
    ( k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f2718,f279])).

fof(f11851,plain,
    ( k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1)) = k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f11825,f11505])).

fof(f19018,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),sK1))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56 ),
    inference(forward_demodulation,[],[f18992,f569])).

fof(f569,plain,
    ( k7_lattices(sK0,k5_lattices(sK0)) = k6_lattices(sK0)
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f568])).

fof(f18992,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),sK1) = k2_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),sK1),sK1))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(resolution,[],[f3494,f475])).

fof(f3494,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k2_lattices(sK0,k7_lattices(sK0,X9),sK1) = k2_lattices(sK0,k7_lattices(sK0,X9),k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,X9),sK1),sK1)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f1296,f279])).

fof(f1296,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k2_lattices(sK0,k7_lattices(sK0,X16),X15) = k2_lattices(sK0,k7_lattices(sK0,X16),k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,X16),X15),X15))
        | ~ m1_subset_1(X16,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1295,f214])).

fof(f1295,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k2_lattices(sK0,k7_lattices(sK0,X16),X15) = k2_lattices(sK0,k7_lattices(sK0,X16),k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,X16),X15),X15))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1283,f235])).

fof(f1283,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k2_lattices(sK0,k7_lattices(sK0,X16),X15) = k2_lattices(sK0,k7_lattices(sK0,X16),k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,X16),X15),X15))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f789,f184])).

fof(f789,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f788,f214])).

fof(f788,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f787,f400])).

fof(f787,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_56 ),
    inference(resolution,[],[f632,f198])).

fof(f632,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k2_lattices(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X4) = k2_lattices(sK0,X3,k1_lattices(sK0,k2_lattices(sK0,X3,X4),X4)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( ! [X4,X3] :
        ( k2_lattices(sK0,X3,X4) = k2_lattices(sK0,X3,k1_lattices(sK0,k2_lattices(sK0,X3,X4),X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_lattices(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_lattices(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_56 ),
    inference(superposition,[],[f605,f379])).

fof(f19228,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f19227,f11949])).

fof(f11949,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),sK1) = k1_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f11919,f11825])).

fof(f11919,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f3128,f279])).

fof(f3128,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),X1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f3121,f620])).

fof(f3121,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),X1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f3101])).

fof(f3101,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),X1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f1455,f334])).

fof(f19227,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),sK1))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56 ),
    inference(forward_demodulation,[],[f19201,f569])).

fof(f19201,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),sK1) = k2_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),sK1),sK1))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(resolution,[],[f3572,f475])).

fof(f3572,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k4_lattices(sK0,k7_lattices(sK0,X9),sK1) = k2_lattices(sK0,k7_lattices(sK0,X9),k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,X9),sK1),sK1)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f1330,f279])).

fof(f1330,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | k4_lattices(sK0,k7_lattices(sK0,X15),X16) = k2_lattices(sK0,k7_lattices(sK0,X15),k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,X15),X16),X16))
        | ~ m1_subset_1(X15,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1329,f214])).

fof(f1329,plain,
    ( ! [X15,X16] :
        ( k4_lattices(sK0,k7_lattices(sK0,X15),X16) = k2_lattices(sK0,k7_lattices(sK0,X15),k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,X15),X16),X16))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1317,f235])).

fof(f1317,plain,
    ( ! [X15,X16] :
        ( k4_lattices(sK0,k7_lattices(sK0,X15),X16) = k2_lattices(sK0,k7_lattices(sK0,X15),k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,X15),X16),X16))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f824,f184])).

fof(f824,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X3,X4) = k2_lattices(sK0,X3,k1_lattices(sK0,k4_lattices(sK0,X3,X4),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f815,f421])).

fof(f815,plain,
    ( ! [X4,X3] :
        ( k4_lattices(sK0,X3,X4) = k2_lattices(sK0,X3,k1_lattices(sK0,k4_lattices(sK0,X3,X4),X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X3,X4),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f809])).

fof(f809,plain,
    ( ! [X4,X3] :
        ( k4_lattices(sK0,X3,X4) = k2_lattices(sK0,X3,k1_lattices(sK0,k4_lattices(sK0,X3,X4),X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k4_lattices(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f633,f379])).

fof(f19293,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_40
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_314
    | ~ spl13_472 ),
    inference(backward_demodulation,[],[f19267,f19228])).

fof(f18262,plain,
    ( spl13_472
    | spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_318 ),
    inference(avatar_split_clause,[],[f17568,f10657,f10523,f6959,f1187,f619,f604,f399,f396,f357,f278,f213,f18260])).

fof(f17568,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k6_lattices(sK0),sK1)) = sK1
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_318 ),
    inference(forward_demodulation,[],[f17540,f17279])).

fof(f17279,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k6_lattices(sK0))) = sK1
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_314
    | ~ spl13_318 ),
    inference(forward_demodulation,[],[f17278,f10524])).

fof(f17278,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k6_lattices(sK0)))
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212
    | ~ spl13_318 ),
    inference(forward_demodulation,[],[f17257,f10658])).

fof(f17257,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k6_lattices(sK0))) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k6_lattices(sK0)))
    | ~ spl13_10
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(resolution,[],[f7000,f620])).

fof(f17540,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,k6_lattices(sK0),sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,k5_lattices(sK0),sK2),k6_lattices(sK0)))
    | ~ spl13_1
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_94
    | ~ spl13_212 ),
    inference(resolution,[],[f7007,f620])).

fof(f10659,plain,
    ( spl13_318
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_308 ),
    inference(avatar_split_clause,[],[f10377,f10158,f619,f568,f559,f399,f396,f357,f351,f319,f278,f234,f220,f213,f10657])).

fof(f559,plain,
    ( spl13_46
  <=> m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f10158,plain,
    ( spl13_308
  <=> k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_308])])).

fof(f10377,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_308 ),
    inference(subsumption_resolution,[],[f10273,f279])).

fof(f10273,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_308 ),
    inference(superposition,[],[f10159,f746])).

fof(f746,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,X0,k6_lattices(sK0)) = k6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f742,f620])).

fof(f742,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,X0,k6_lattices(sK0)) = k6_lattices(sK0)
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48 ),
    inference(duplicate_literal_removal,[],[f732])).

fof(f732,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,X0,k6_lattices(sK0)) = k6_lattices(sK0)
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48 ),
    inference(superposition,[],[f415,f596])).

fof(f596,plain,
    ( ! [X1] :
        ( k4_lattices(sK0,X1,k6_lattices(sK0)) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f440,f595])).

fof(f595,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl13_46
    | ~ spl13_48 ),
    inference(forward_demodulation,[],[f560,f569])).

fof(f560,plain,
    ( m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f559])).

fof(f440,plain,
    ( ! [X1] :
        ( k4_lattices(sK0,X1,k6_lattices(sK0)) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( ! [X1] :
        ( k4_lattices(sK0,X1,k6_lattices(sK0)) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(superposition,[],[f408,f334])).

fof(f10159,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) = sK1
    | ~ spl13_308 ),
    inference(avatar_component_clause,[],[f10158])).

fof(f10525,plain,
    ( spl13_314
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_188
    | ~ spl13_308 ),
    inference(avatar_split_clause,[],[f10378,f10158,f5797,f619,f568,f559,f399,f396,f357,f351,f319,f278,f271,f234,f220,f213,f10523])).

fof(f5797,plain,
    ( spl13_188
  <=> k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k6_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_188])])).

fof(f10378,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_188
    | ~ spl13_308 ),
    inference(backward_demodulation,[],[f10377,f6097])).

fof(f6097,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_188 ),
    inference(subsumption_resolution,[],[f6033,f272])).

fof(f6033,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_58
    | ~ spl13_188 ),
    inference(superposition,[],[f5798,f746])).

fof(f5798,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k6_lattices(sK0)))
    | ~ spl13_188 ),
    inference(avatar_component_clause,[],[f5797])).

fof(f10160,plain,
    ( spl13_308
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_244 ),
    inference(avatar_split_clause,[],[f10145,f7871,f619,f604,f568,f559,f399,f396,f357,f319,f278,f234,f220,f213,f10158])).

fof(f7871,plain,
    ( spl13_244
  <=> k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_244])])).

fof(f10145,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) = sK1
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58
    | ~ spl13_244 ),
    inference(forward_demodulation,[],[f10118,f7872])).

fof(f7872,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl13_244 ),
    inference(avatar_component_clause,[],[f7871])).

fof(f10118,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(resolution,[],[f3129,f279])).

fof(f3129,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k1_lattices(sK0,k4_lattices(sK0,X7,sK1),X7) = k2_lattices(sK0,X7,k1_lattices(sK0,sK1,k6_lattices(sK0))) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f3117,f620])).

fof(f3117,plain,
    ( ! [X7] :
        ( k1_lattices(sK0,k4_lattices(sK0,X7,sK1),X7) = k2_lattices(sK0,X7,k1_lattices(sK0,sK1,k6_lattices(sK0)))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f3106])).

fof(f3106,plain,
    ( ! [X7] :
        ( k1_lattices(sK0,k4_lattices(sK0,X7,sK1),X7) = k2_lattices(sK0,X7,k1_lattices(sK0,sK1,k6_lattices(sK0)))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56 ),
    inference(superposition,[],[f1455,f596])).

fof(f7873,plain,
    ( spl13_244
    | spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_206 ),
    inference(avatar_split_clause,[],[f6759,f6517,f351,f278,f234,f213,f7871])).

fof(f6517,plain,
    ( spl13_206
  <=> k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_206])])).

fof(f6759,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_206 ),
    inference(subsumption_resolution,[],[f6758,f279])).

fof(f6758,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_206 ),
    inference(duplicate_literal_removal,[],[f6651])).

fof(f6651,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_206 ),
    inference(superposition,[],[f379,f6518])).

fof(f6518,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl13_206 ),
    inference(avatar_component_clause,[],[f6517])).

fof(f6990,plain,
    ( spl13_1
    | ~ spl13_8
    | ~ spl13_36
    | ~ spl13_40
    | spl13_213 ),
    inference(avatar_contradiction_clause,[],[f6989])).

fof(f6989,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_213 ),
    inference(subsumption_resolution,[],[f6988,f214])).

fof(f6988,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_8
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_213 ),
    inference(subsumption_resolution,[],[f6987,f272])).

fof(f6987,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_213 ),
    inference(subsumption_resolution,[],[f6986,f475])).

fof(f6986,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_36
    | ~ spl13_213 ),
    inference(subsumption_resolution,[],[f6982,f455])).

fof(f6982,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_213 ),
    inference(resolution,[],[f6963,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',dt_k1_lattices)).

fof(f6963,plain,
    ( ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0))
    | ~ spl13_213 ),
    inference(avatar_component_clause,[],[f6962])).

fof(f6962,plain,
    ( spl13_213
  <=> ~ m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_213])])).

fof(f6519,plain,
    ( spl13_206
    | spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_200 ),
    inference(avatar_split_clause,[],[f6471,f6202,f399,f396,f357,f351,f278,f234,f213,f6517])).

fof(f6202,plain,
    ( spl13_200
  <=> k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_200])])).

fof(f6471,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_200 ),
    inference(subsumption_resolution,[],[f6470,f279])).

fof(f6470,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_200 ),
    inference(duplicate_literal_removal,[],[f6404])).

fof(f6404,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_200 ),
    inference(superposition,[],[f6203,f670])).

fof(f6203,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1))
    | ~ spl13_200 ),
    inference(avatar_component_clause,[],[f6202])).

fof(f6204,plain,
    ( spl13_200
    | spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f2150,f604,f399,f396,f351,f278,f234,f213,f6202])).

fof(f2150,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f1313,f279])).

fof(f1313,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X9) = k2_lattices(sK0,sK1,k1_lattices(sK0,k4_lattices(sK0,sK1,X9),X9)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_56 ),
    inference(resolution,[],[f824,f279])).

fof(f5799,plain,
    ( spl13_188
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f2304,f619,f604,f568,f559,f399,f396,f357,f319,f305,f278,f271,f234,f220,f213,f5797])).

fof(f2304,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k6_lattices(sK0)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f2303,f279])).

fof(f2303,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k6_lattices(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f2291,f620])).

fof(f2291,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,k6_lattices(sK0)))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_32
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_56 ),
    inference(superposition,[],[f1992,f596])).

fof(f1992,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1991,f279])).

fof(f1991,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f1984])).

fof(f1984,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,X0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f1141,f397])).

fof(f1141,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1140,f272])).

fof(f1140,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1134,f279])).

fof(f1134,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,X1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,X1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f634,f306])).

fof(f1951,plain,
    ( spl13_16
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_44
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f1905,f1826,f1781,f495,f474,f454,f357,f351,f345,f298,f234,f220,f213,f305])).

fof(f345,plain,
    ( spl13_24
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f1781,plain,
    ( spl13_110
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f1826,plain,
    ( spl13_112
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f1905,plain,
    ( k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_44
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f1904,f1827])).

fof(f1827,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1904,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_44
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f1903,f330])).

fof(f330,plain,
    ( ! [X1] :
        ( r3_lattices(sK0,k5_lattices(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f329,f235])).

fof(f329,plain,
    ( ! [X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f328,f214])).

fof(f328,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl13_2
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f324,f221])).

fof(f324,plain,
    ( ! [X1] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl13_14 ),
    inference(resolution,[],[f299,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattices(X0,k5_lattices(X0),X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t41_lattices)).

fof(f1903,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ r3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_44
    | ~ spl13_110 ),
    inference(subsumption_resolution,[],[f1810,f475])).

fof(f1810,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ r3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_44
    | ~ spl13_110 ),
    inference(resolution,[],[f1782,f556])).

fof(f556,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | X2 = X3
        | ~ r3_lattices(sK0,X3,X2) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(duplicate_literal_removal,[],[f555])).

fof(f555,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X3)
        | X2 = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(resolution,[],[f507,f385])).

fof(f385,plain,
    ( ! [X12,X13] :
        ( r1_lattices(sK0,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X12,X13) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f378,f358])).

fof(f378,plain,
    ( ! [X12,X13] :
        ( ~ v6_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | r1_lattices(sK0,X12,X13)
        | ~ r3_lattices(sK0,X12,X13) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f368,f352])).

fof(f368,plain,
    ( ! [X12,X13] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | r1_lattices(sK0,X12,X13)
        | ~ r3_lattices(sK0,X12,X13) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f265,f346])).

fof(f346,plain,
    ( v9_lattices(sK0)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f345])).

fof(f265,plain,
    ( ! [X12,X13] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | r1_lattices(sK0,X12,X13)
        | ~ r3_lattices(sK0,X12,X13) )
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f251,f214])).

fof(f251,plain,
    ( ! [X12,X13] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | r1_lattices(sK0,X12,X13)
        | ~ r3_lattices(sK0,X12,X13) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',redefinition_r3_lattices)).

fof(f507,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X1,X0)
        | X0 = X1 )
    | ~ spl13_1
    | ~ spl13_36
    | ~ spl13_44 ),
    inference(subsumption_resolution,[],[f466,f496])).

fof(f466,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X1,X0)
        | X0 = X1 )
    | ~ spl13_1
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f237,f455])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X1,X0)
        | X0 = X1 )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t26_lattices)).

fof(f1782,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ spl13_110 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1927,plain,
    ( ~ spl13_85
    | ~ spl13_10
    | ~ spl13_34
    | ~ spl13_82
    | spl13_93 ),
    inference(avatar_split_clause,[],[f1915,f1128,f976,f451,f278,f982])).

fof(f451,plain,
    ( spl13_34
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | k1_lattices(sK0,X2,X3) != X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f1128,plain,
    ( spl13_93
  <=> ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_93])])).

fof(f1915,plain,
    ( k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_10
    | ~ spl13_34
    | ~ spl13_82
    | ~ spl13_93 ),
    inference(subsumption_resolution,[],[f1194,f977])).

fof(f1194,plain,
    ( k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_10
    | ~ spl13_34
    | ~ spl13_93 ),
    inference(subsumption_resolution,[],[f1142,f279])).

fof(f1142,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_34
    | ~ spl13_93 ),
    inference(resolution,[],[f1129,f452])).

fof(f452,plain,
    ( ! [X2,X3] :
        ( r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) != X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f451])).

fof(f1129,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_93 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1896,plain,
    ( spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_32
    | spl13_113 ),
    inference(avatar_contradiction_clause,[],[f1895])).

fof(f1895,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_32
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f1894,f214])).

fof(f1894,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_32
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f1893,f272])).

fof(f1893,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_10
    | ~ spl13_28
    | ~ spl13_32
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f1892,f279])).

fof(f1892,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_28
    | ~ spl13_32
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f1891,f400])).

fof(f1891,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_28
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f1887,f358])).

fof(f1887,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_113 ),
    inference(resolution,[],[f1830,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',dt_k4_lattices)).

fof(f1830,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_113 ),
    inference(avatar_component_clause,[],[f1829])).

fof(f1829,plain,
    ( spl13_113
  <=> ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_113])])).

fof(f1783,plain,
    ( spl13_110
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f1756,f1702,f396,f278,f271,f1781])).

fof(f1702,plain,
    ( spl13_108
  <=> r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f1756,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_108 ),
    inference(subsumption_resolution,[],[f1755,f272])).

fof(f1755,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_10
    | ~ spl13_30
    | ~ spl13_108 ),
    inference(subsumption_resolution,[],[f1752,f279])).

fof(f1752,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_108 ),
    inference(superposition,[],[f1703,f397])).

fof(f1703,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ spl13_108 ),
    inference(avatar_component_clause,[],[f1702])).

fof(f1704,plain,
    ( spl13_108
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f1693,f976,f572,f396,f357,f351,f345,f311,f278,f271,f234,f227,f220,f213,f1702])).

fof(f311,plain,
    ( spl13_18
  <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f572,plain,
    ( spl13_50
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f1693,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f1691,f272])).

fof(f1691,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(duplicate_literal_removal,[],[f1684])).

fof(f1684,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k5_lattices(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(superposition,[],[f1018,f261])).

fof(f261,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,k7_lattices(sK0,X4),X4) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f260,f214])).

fof(f260,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k4_lattices(sK0,k7_lattices(sK0,X4),X4) = k5_lattices(sK0) )
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f259,f228])).

fof(f259,plain,
    ( ! [X4] :
        ( ~ v17_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k4_lattices(sK0,k7_lattices(sK0,X4),X4) = k5_lattices(sK0) )
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f247,f221])).

fof(f247,plain,
    ( ! [X4] :
        ( ~ v10_lattices(sK0)
        | ~ v17_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k4_lattices(sK0,k7_lattices(sK0,X4),X4) = k5_lattices(sK0) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t47_lattices)).

fof(f1018,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,k7_lattices(sK0,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f1015,f977])).

fof(f1015,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,k7_lattices(sK0,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(duplicate_literal_removal,[],[f1014])).

fof(f1014,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,k7_lattices(sK0,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_30
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(superposition,[],[f993,f397])).

fof(f993,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k7_lattices(sK0,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_50
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f766,f977])).

fof(f766,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k7_lattices(sK0,sK2),X0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f759,f279])).

fof(f759,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,k7_lattices(sK0,sK2),X0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(resolution,[],[f588,f312])).

fof(f312,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f311])).

fof(f588,plain,
    ( ! [X4,X5,X3] :
        ( ~ r3_lattices(sK0,X3,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X3,X4),k2_lattices(sK0,X5,X4)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(duplicate_literal_removal,[],[f587])).

fof(f587,plain,
    ( ! [X4,X5,X3] :
        ( r1_lattices(sK0,k2_lattices(sK0,X3,X4),k2_lattices(sK0,X5,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X5) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(resolution,[],[f573,f385])).

fof(f573,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f572])).

fof(f1189,plain,
    ( spl13_94
    | spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f1178,f604,f474,f396,f351,f305,f278,f271,f234,f213,f1187])).

fof(f1178,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1177,f279])).

fof(f1177,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_40
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1174,f475])).

fof(f1174,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(duplicate_literal_removal,[],[f1168])).

fof(f1168,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k1_lattices(sK0,k5_lattices(sK0),sK2))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f1139,f379])).

fof(f1139,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k2_lattices(sK0,sK1,X0),k5_lattices(sK0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,X0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1138,f272])).

fof(f1138,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k2_lattices(sK0,sK1,X0),k5_lattices(sK0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,X0,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_10
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f1133,f279])).

fof(f1133,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k2_lattices(sK0,sK1,X0),k5_lattices(sK0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,X0,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_16
    | ~ spl13_30
    | ~ spl13_56 ),
    inference(superposition,[],[f633,f306])).

fof(f1130,plain,
    ( ~ spl13_93
    | spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | spl13_19
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f1123,f976,f357,f351,f345,f308,f278,f234,f213,f1128])).

fof(f308,plain,
    ( spl13_19
  <=> ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f1123,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_19
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f1122,f279])).

fof(f1122,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_19
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f1121,f977])).

fof(f1121,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_19
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28 ),
    inference(resolution,[],[f309,f386])).

fof(f386,plain,
    ( ! [X10,X11] :
        ( r3_lattices(sK0,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X10,X11)
        | ~ m1_subset_1(X10,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f377,f358])).

fof(f377,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X10,X11)
        | r3_lattices(sK0,X10,X11) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f369,f352])).

fof(f369,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X10,X11)
        | r3_lattices(sK0,X10,X11) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f264,f346])).

fof(f264,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X10,X11)
        | r3_lattices(sK0,X10,X11) )
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f250,f214])).

fof(f250,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X10,X11)
        | r3_lattices(sK0,X10,X11) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f309,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f308])).

fof(f992,plain,
    ( spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | spl13_83 ),
    inference(avatar_contradiction_clause,[],[f991])).

fof(f991,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_83 ),
    inference(subsumption_resolution,[],[f990,f214])).

fof(f990,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_83 ),
    inference(subsumption_resolution,[],[f989,f272])).

fof(f989,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_83 ),
    inference(subsumption_resolution,[],[f988,f235])).

fof(f988,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_83 ),
    inference(resolution,[],[f980,f184])).

fof(f980,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_83 ),
    inference(avatar_component_clause,[],[f979])).

fof(f979,plain,
    ( spl13_83
  <=> ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_83])])).

fof(f621,plain,
    ( spl13_58
    | ~ spl13_46
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f595,f568,f559,f619])).

fof(f614,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_55 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f612,f235])).

fof(f612,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f611,f228])).

fof(f611,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f610,f214])).

fof(f610,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_55 ),
    inference(resolution,[],[f602,f151])).

fof(f151,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',cc5_lattices)).

fof(f602,plain,
    ( ~ v11_lattices(sK0)
    | ~ spl13_55 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl13_55
  <=> ~ v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f606,plain,
    ( ~ spl13_55
    | spl13_56
    | spl13_1
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f262,f234,f213,f604,f601])).

fof(f262,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X5,X6),k2_lattices(sK0,X5,X7)) = k2_lattices(sK0,X5,k1_lattices(sK0,X6,X7))
        | ~ v11_lattices(sK0) )
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f248,f214])).

fof(f248,plain,
    ( ! [X6,X7,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X5,X6),k2_lattices(sK0,X5,X7)) = k2_lattices(sK0,X5,k1_lattices(sK0,X6,X7))
        | ~ v11_lattices(sK0) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f171])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
      | ~ v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',d11_lattices)).

fof(f594,plain,
    ( spl13_1
    | ~ spl13_6
    | ~ spl13_40
    | spl13_47 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_40
    | ~ spl13_47 ),
    inference(subsumption_resolution,[],[f592,f214])).

fof(f592,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_40
    | ~ spl13_47 ),
    inference(subsumption_resolution,[],[f591,f475])).

fof(f591,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_47 ),
    inference(subsumption_resolution,[],[f590,f235])).

fof(f590,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_47 ),
    inference(resolution,[],[f563,f184])).

fof(f563,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl13_47 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl13_47
  <=> ~ m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_47])])).

fof(f585,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | spl13_53 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_53 ),
    inference(subsumption_resolution,[],[f583,f235])).

fof(f583,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_53 ),
    inference(subsumption_resolution,[],[f582,f221])).

fof(f582,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_53 ),
    inference(subsumption_resolution,[],[f581,f214])).

fof(f581,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_53 ),
    inference(resolution,[],[f579,f157])).

fof(f157,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',cc1_lattices)).

fof(f579,plain,
    ( ~ v7_lattices(sK0)
    | ~ spl13_53 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl13_53
  <=> ~ v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_53])])).

fof(f580,plain,
    ( spl13_50
    | ~ spl13_53
    | spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f376,f351,f345,f234,f213,f578,f572])).

fof(f376,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f370,f352])).

fof(f370,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f255,f346])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f245,f214])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f160])).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v7_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t27_lattices)).

fof(f570,plain,
    ( ~ spl13_47
    | spl13_48
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f553,f492,f474,f298,f234,f227,f220,f213,f568,f562])).

fof(f553,plain,
    ( k7_lattices(sK0,k5_lattices(sK0)) = k6_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_42 ),
    inference(subsumption_resolution,[],[f541,f475])).

fof(f541,plain,
    ( k7_lattices(sK0,k5_lattices(sK0)) = k6_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_40
    | ~ spl13_42 ),
    inference(superposition,[],[f528,f258])).

fof(f505,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | spl13_45 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f503,f235])).

fof(f503,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f502,f221])).

fof(f502,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_45 ),
    inference(subsumption_resolution,[],[f501,f214])).

fof(f501,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_45 ),
    inference(resolution,[],[f499,f154])).

fof(f154,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f499,plain,
    ( ~ v4_lattices(sK0)
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl13_45
  <=> ~ v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f500,plain,
    ( spl13_42
    | ~ spl13_45
    | spl13_1
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f463,f454,f213,f498,f492])).

fof(f463,plain,
    ( ! [X8,X9] :
        ( ~ v4_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k3_lattices(sK0,X8,X9) = k3_lattices(sK0,X9,X8) )
    | ~ spl13_1
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f241,f455])).

fof(f241,plain,
    ( ! [X8,X9] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k3_lattices(sK0,X8,X9) = k3_lattices(sK0,X9,X8) )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',commutativity_k3_lattices)).

fof(f490,plain,
    ( spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_38 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_38 ),
    inference(subsumption_resolution,[],[f272,f484])).

fof(f484,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_38 ),
    inference(subsumption_resolution,[],[f483,f214])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_6
    | ~ spl13_38 ),
    inference(subsumption_resolution,[],[f482,f235])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_38 ),
    inference(duplicate_literal_removal,[],[f481])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_38 ),
    inference(resolution,[],[f469,f184])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl13_38
  <=> ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f476,plain,
    ( spl13_38
    | spl13_40
    | spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f449,f399,f396,f234,f227,f220,f213,f474,f468])).

fof(f449,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_30
    | ~ spl13_32 ),
    inference(superposition,[],[f421,f261])).

fof(f462,plain,
    ( ~ spl13_6
    | spl13_37 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_37 ),
    inference(subsumption_resolution,[],[f460,f235])).

fof(f460,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_37 ),
    inference(resolution,[],[f458,f148])).

fof(f148,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',dt_l3_lattices)).

fof(f458,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl13_37 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl13_37
  <=> ~ l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).

fof(f459,plain,
    ( spl13_34
    | ~ spl13_37
    | spl13_1 ),
    inference(avatar_split_clause,[],[f238,f213,f457,f451])).

fof(f238,plain,
    ( ! [X2,X3] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) != X3
        | r1_lattices(sK0,X2,X3) )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',d3_lattices)).

fof(f407,plain,
    ( ~ spl13_6
    | spl13_33 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f405,f235])).

fof(f405,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_33 ),
    inference(resolution,[],[f403,f147])).

fof(f147,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f403,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl13_33
  <=> ~ l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f404,plain,
    ( spl13_30
    | ~ spl13_33
    | spl13_1
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f387,f357,f213,f402,f396])).

fof(f387,plain,
    ( ! [X12,X13] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | k4_lattices(sK0,X12,X13) = k2_lattices(sK0,X12,X13) )
    | ~ spl13_1
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f243,f358])).

fof(f243,plain,
    ( ! [X12,X13] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | k4_lattices(sK0,X12,X13) = k2_lattices(sK0,X12,X13) )
    | ~ spl13_1 ),
    inference(resolution,[],[f214,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',redefinition_k4_lattices)).

fof(f384,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | spl13_29 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f382,f235])).

fof(f382,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f381,f221])).

fof(f381,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f380,f214])).

fof(f380,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_29 ),
    inference(resolution,[],[f361,f156])).

fof(f156,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f361,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl13_29 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl13_29
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f375,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | spl13_27 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f373,f235])).

fof(f373,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f372,f221])).

fof(f372,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f371,f214])).

fof(f371,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_27 ),
    inference(resolution,[],[f355,f158])).

fof(f158,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f355,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl13_27
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f367,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | spl13_25 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f365,f235])).

fof(f365,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f364,f221])).

fof(f364,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f363,f214])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_25 ),
    inference(resolution,[],[f349,f159])).

fof(f159,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f349,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl13_25
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f322,plain,
    ( ~ spl13_17
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f314,f311,f302])).

fof(f302,plain,
    ( spl13_17
  <=> k4_lattices(sK0,sK1,sK2) != k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f314,plain,
    ( k4_lattices(sK0,sK1,sK2) != k5_lattices(sK0)
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f131,f312])).

fof(f131,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,sK1,sK2) != k5_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',t52_lattices)).

fof(f321,plain,
    ( spl13_20
    | spl13_1
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f293,f285,f234,f213,f319])).

fof(f285,plain,
    ( spl13_12
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f293,plain,
    ( v14_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f292,f235])).

fof(f292,plain,
    ( ~ l3_lattices(sK0)
    | v14_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f289,f214])).

fof(f289,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v14_lattices(sK0)
    | ~ spl13_12 ),
    inference(resolution,[],[f286,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v14_lattices(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t52_lattices.p',cc4_lattices)).

fof(f286,plain,
    ( v15_lattices(sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f285])).

fof(f313,plain,
    ( spl13_16
    | spl13_18 ),
    inference(avatar_split_clause,[],[f130,f311,f305])).

fof(f130,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f300,plain,
    ( spl13_14
    | spl13_1
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f291,f285,f234,f213,f298])).

fof(f291,plain,
    ( v13_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f290,f235])).

fof(f290,plain,
    ( ~ l3_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f288,f214])).

fof(f288,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl13_12 ),
    inference(resolution,[],[f286,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f287,plain,
    ( spl13_12
    | spl13_1
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f254,f234,f227,f213,f285])).

fof(f254,plain,
    ( v15_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f253,f228])).

fof(f253,plain,
    ( ~ v17_lattices(sK0)
    | v15_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f244,f214])).

fof(f244,plain,
    ( v2_struct_0(sK0)
    | ~ v17_lattices(sK0)
    | v15_lattices(sK0)
    | ~ spl13_6 ),
    inference(resolution,[],[f235,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | v15_lattices(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f280,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f133,f278])).

fof(f133,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f273,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f132,f271])).

fof(f132,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f236,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f137,f234])).

fof(f137,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f229,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f136,f227])).

fof(f136,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f222,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f135,f220])).

fof(f135,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f215,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f134,f213])).

fof(f134,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
