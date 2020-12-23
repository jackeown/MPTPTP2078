%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t43_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 310 expanded)
%              Number of leaves         :   25 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  575 (1219 expanded)
%              Number of equality atoms :   74 ( 107 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f130,f134,f138,f156,f160,f164,f215,f229,f1129,f2003,f2007,f2011,f2072,f2595,f2596])).

fof(f2596,plain,
    ( k6_lattices(sK0) != k1_lattices(sK0,sK1,k6_lattices(sK0))
    | k3_lattices(sK0,sK1,k6_lattices(sK0)) != k1_lattices(sK0,sK1,k6_lattices(sK0))
    | k4_lattices(sK0,sK1,k6_lattices(sK0)) != k2_lattices(sK0,sK1,k6_lattices(sK0))
    | k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k6_lattices(sK0))) != sK1
    | k4_lattices(sK0,sK1,k6_lattices(sK0)) = sK1 ),
    introduced(theory_axiom,[])).

fof(f2595,plain,
    ( spl9_180
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f2538,f227,f162,f158,f132,f124,f2593])).

fof(f2593,plain,
    ( spl9_180
  <=> k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f124,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f132,plain,
    ( spl9_4
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f158,plain,
    ( spl9_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f162,plain,
    ( spl9_12
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f227,plain,
    ( spl9_22
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f2538,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(resolution,[],[f282,f159])).

fof(f159,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f282,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f281,f125])).

fof(f125,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f281,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f280,f133])).

fof(f133,plain,
    ( v14_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ v14_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f261,f163])).

fof(f163,plain,
    ( l2_lattices(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f261,plain,
    ( ! [X1] :
        ( ~ l2_lattices(sK0)
        | ~ v14_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl9_22 ),
    inference(resolution,[],[f228,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X2,X1) = X1
      | k6_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',d17_lattices)).

fof(f228,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f2072,plain,
    ( ~ spl9_171
    | spl9_17
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2068,f2005,f213,f2070])).

fof(f2070,plain,
    ( spl9_171
  <=> k4_lattices(sK0,sK1,k6_lattices(sK0)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_171])])).

fof(f213,plain,
    ( spl9_17
  <=> k4_lattices(sK0,k6_lattices(sK0),sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f2005,plain,
    ( spl9_142
  <=> k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f2068,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) != sK1
    | ~ spl9_17
    | ~ spl9_142 ),
    inference(superposition,[],[f214,f2006])).

fof(f2006,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl9_142 ),
    inference(avatar_component_clause,[],[f2005])).

fof(f214,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) != sK1
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f213])).

fof(f2011,plain,
    ( spl9_144
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f362,f227,f162,f158,f136,f128,f124,f2009])).

fof(f2009,plain,
    ( spl9_144
  <=> k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f128,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f136,plain,
    ( spl9_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f362,plain,
    ( k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(resolution,[],[f201,f228])).

fof(f201,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X6) = k1_lattices(sK0,sK1,X6) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f200,f125])).

fof(f200,plain,
    ( ! [X6] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X6) = k1_lattices(sK0,sK1,X6) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f199,f163])).

fof(f199,plain,
    ( ! [X6] :
        ( ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X6) = k1_lattices(sK0,sK1,X6) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f173,f148])).

fof(f148,plain,
    ( v4_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f147,f129])).

fof(f129,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f147,plain,
    ( ~ v10_lattices(sK0)
    | v4_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f141,f125])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v4_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f42])).

fof(f42,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',cc1_lattices)).

fof(f137,plain,
    ( l3_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f173,plain,
    ( ! [X6] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k3_lattices(sK0,sK1,X6) = k1_lattices(sK0,sK1,X6) )
    | ~ spl9_10 ),
    inference(resolution,[],[f159,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',redefinition_k3_lattices)).

fof(f2007,plain,
    ( spl9_142
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f346,f227,f158,f154,f136,f128,f124,f2005])).

fof(f154,plain,
    ( spl9_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f346,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(resolution,[],[f182,f228])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,sK1) = k4_lattices(sK0,sK1,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f181,f125])).

fof(f181,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,sK1) = k4_lattices(sK0,sK1,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f180,f155])).

fof(f155,plain,
    ( l1_lattices(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,sK1) = k4_lattices(sK0,sK1,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f166,f150])).

fof(f150,plain,
    ( v6_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f149,f129])).

fof(f149,plain,
    ( ~ v10_lattices(sK0)
    | v6_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f142,f125])).

fof(f142,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v6_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,sK1) = k4_lattices(sK0,sK1,X1) )
    | ~ spl9_10 ),
    inference(resolution,[],[f159,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',commutativity_k4_lattices)).

fof(f2003,plain,
    ( spl9_140
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f338,f227,f158,f154,f136,f128,f124,f2001])).

fof(f2001,plain,
    ( spl9_140
  <=> k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f338,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(resolution,[],[f179,f228])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f178,f125])).

fof(f178,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f177,f155])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f165,f150])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f159,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',redefinition_k4_lattices)).

fof(f1129,plain,
    ( spl9_108
    | spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f705,f227,f162,f158,f136,f128,f124,f1127])).

fof(f1127,plain,
    ( spl9_108
  <=> k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k6_lattices(sK0))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f705,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k6_lattices(sK0))) = sK1
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f354,f362])).

fof(f354,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0))) = sK1
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(resolution,[],[f196,f228])).

fof(f196,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X4)) = sK1 )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f195,f152])).

fof(f152,plain,
    ( v9_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f151,f129])).

fof(f151,plain,
    ( ~ v10_lattices(sK0)
    | v9_lattices(sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f143,f125])).

fof(f143,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f195,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X4)) = sK1
        | ~ v9_lattices(sK0) )
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f194,f125])).

fof(f194,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X4)) = sK1
        | ~ v9_lattices(sK0) )
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f171,f137])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X4)) = sK1
        | ~ v9_lattices(sK0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f159,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',d9_lattices)).

fof(f229,plain,
    ( spl9_22
    | spl9_1
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f225,f162,f124,f227])).

fof(f225,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f224,f125])).

fof(f224,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(resolution,[],[f163,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',dt_k6_lattices)).

fof(f215,plain,(
    ~ spl9_17 ),
    inference(avatar_split_clause,[],[f83,f213])).

fof(f83,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',t43_lattices)).

fof(f164,plain,
    ( spl9_12
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f140,f136,f162])).

fof(f140,plain,
    ( l2_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',dt_l3_lattices)).

fof(f160,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f82,f158])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f156,plain,
    ( spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f139,f136,f154])).

fof(f139,plain,
    ( l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f137,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f87,f136])).

fof(f87,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f134,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f86,f132])).

fof(f86,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f130,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f85,f128])).

fof(f85,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f84,f124])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
