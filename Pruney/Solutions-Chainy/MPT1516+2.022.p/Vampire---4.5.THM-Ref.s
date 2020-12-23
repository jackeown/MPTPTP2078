%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:52 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 538 expanded)
%              Number of leaves         :   33 ( 196 expanded)
%              Depth                    :   21
%              Number of atoms          : 1189 (2441 expanded)
%              Number of equality atoms :  128 ( 258 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f186,f208,f213,f218,f235,f240,f248,f259,f281,f366,f379,f388,f422,f526,f534,f555,f566])).

fof(f566,plain,
    ( spl11_1
    | spl11_6
    | ~ spl11_9
    | ~ spl11_20
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | spl11_1
    | spl11_6
    | ~ spl11_9
    | ~ spl11_20
    | spl11_21 ),
    inference(subsumption_resolution,[],[f564,f185])).

fof(f185,plain,
    ( ~ v13_lattices(sK0)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl11_6
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f564,plain,
    ( v13_lattices(sK0)
    | spl11_1
    | ~ spl11_9
    | ~ spl11_20
    | spl11_21 ),
    inference(subsumption_resolution,[],[f563,f111])).

fof(f111,plain,
    ( ~ v2_struct_0(sK0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl11_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f563,plain,
    ( v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl11_9
    | ~ spl11_20
    | spl11_21 ),
    inference(subsumption_resolution,[],[f562,f524])).

fof(f524,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl11_20
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f562,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl11_9
    | spl11_21 ),
    inference(subsumption_resolution,[],[f561,f206])).

fof(f206,plain,
    ( l1_lattices(sK0)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl11_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f561,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | spl11_21 ),
    inference(resolution,[],[f554,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f554,plain,
    ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_21 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl11_21
  <=> m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f555,plain,
    ( ~ spl11_21
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f543,f523,f279,f232,f228,f225,f124,f119,f114,f109,f552])).

fof(f114,plain,
    ( spl11_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f119,plain,
    ( spl11_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f124,plain,
    ( spl11_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f225,plain,
    ( spl11_10
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,X3)
        | r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f228,plain,
    ( spl11_11
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f232,plain,
    ( spl11_12
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f279,plain,
    ( spl11_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f543,plain,
    ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f542,f524])).

fof(f542,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(trivial_inequality_removal,[],[f541])).

fof(f541,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(superposition,[],[f280,f497])).

fof(f497,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(resolution,[],[f479,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f479,plain,
    ( ! [X12,X11] :
        ( ~ v1_xboole_0(X11)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),X12) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(resolution,[],[f428,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f428,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f427,f111])).

fof(f427,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f423,f126])).

fof(f126,plain,
    ( l3_lattices(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f423,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(resolution,[],[f323,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f323,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
        | r2_hidden(sK6(sK0,X0,k6_domain_1(u1_struct_0(sK0),X1)),X0) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,k6_domain_1(u1_struct_0(sK0),X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(resolution,[],[f192,f254])).

fof(f254,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X3,X2)
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(resolution,[],[f250,f226])).

fof(f226,plain,
    ( ! [X2,X3] :
        ( r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f225])).

fof(f250,plain,
    ( ! [X10,X9] :
        ( ~ r1_lattices(sK0,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_4
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f242,f233])).

fof(f233,plain,
    ( v8_lattices(sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f242,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl11_1
    | ~ spl11_4
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f137,f229])).

fof(f229,plain,
    ( v9_lattices(sK0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f137,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl11_1
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f133,f126])).

fof(f133,plain,
    ( ! [X10,X9] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,X9,X10) = X9
        | ~ r1_lattices(sK0,X9,X10) )
    | spl11_1 ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f192,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),X2)
        | r2_hidden(sK6(sK0,X3,k6_domain_1(u1_struct_0(sK0),X2)),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(superposition,[],[f165,f156])).

fof(f156,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f155,f126])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f154,f111])).

fof(f154,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f140,f116])).

fof(f116,plain,
    ( v10_lattices(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f140,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 )
    | ~ spl11_3 ),
    inference(resolution,[],[f121,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

fof(f121,plain,
    ( v4_lattice3(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f165,plain,
    ( ! [X8,X7] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8))
        | r2_hidden(sK6(sK0,X7,X8),X7) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f164,f126])).

fof(f164,plain,
    ( ! [X8,X7] :
        ( ~ l3_lattices(sK0)
        | r2_hidden(sK6(sK0,X7,X8),X7)
        | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8)) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f163,f111])).

fof(f163,plain,
    ( ! [X8,X7] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | r2_hidden(sK6(sK0,X7,X8),X7)
        | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8)) )
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f143,f116])).

fof(f143,plain,
    ( ! [X8,X7] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | r2_hidden(sK6(sK0,X7,X8),X7)
        | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8)) )
    | ~ spl11_3 ),
    inference(resolution,[],[f121,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f280,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f279])).

fof(f534,plain,
    ( spl11_1
    | ~ spl11_4
    | spl11_20 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | spl11_1
    | ~ spl11_4
    | spl11_20 ),
    inference(subsumption_resolution,[],[f532,f111])).

fof(f532,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_4
    | spl11_20 ),
    inference(subsumption_resolution,[],[f531,f126])).

fof(f531,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_20 ),
    inference(resolution,[],[f525,f89])).

fof(f525,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_20 ),
    inference(avatar_component_clause,[],[f523])).

fof(f526,plain,
    ( ~ spl11_20
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f517,f419,f363,f232,f228,f225,f205,f183,f179,f124,f119,f114,f109,f523])).

fof(f179,plain,
    ( spl11_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f363,plain,
    ( spl11_17
  <=> k5_lattices(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f419,plain,
    ( spl11_18
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f517,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f516,f421])).

fof(f421,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f419])).

fof(f516,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f506,f181])).

fof(f181,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f506,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | ~ spl11_17 ),
    inference(superposition,[],[f497,f390])).

fof(f390,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(backward_demodulation,[],[f288,f365])).

fof(f365,plain,
    ( k5_lattices(sK0) = sK2(sK0)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f363])).

fof(f288,plain,
    ( ! [X1] :
        ( sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f287,f111])).

fof(f287,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0))
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f283,f206])).

fof(f283,plain,
    ( ! [X1] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0))
        | v2_struct_0(sK0) )
    | ~ spl11_6 ),
    inference(resolution,[],[f184,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK2(X0) = k2_lattices(X0,X2,sK2(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f184,plain,
    ( v13_lattices(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f183])).

fof(f422,plain,
    ( spl11_18
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f415,f363,f205,f183,f109,f419])).

fof(f415,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f414,f184])).

fof(f414,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | spl11_1
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f413,f111])).

fof(f413,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f412,f206])).

fof(f412,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | ~ spl11_17 ),
    inference(superposition,[],[f75,f365])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f388,plain,
    ( spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | spl11_16 ),
    inference(subsumption_resolution,[],[f386,f184])).

fof(f386,plain,
    ( ~ v13_lattices(sK0)
    | spl11_1
    | ~ spl11_9
    | spl11_16 ),
    inference(subsumption_resolution,[],[f385,f111])).

fof(f385,plain,
    ( v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | ~ spl11_9
    | spl11_16 ),
    inference(subsumption_resolution,[],[f384,f206])).

fof(f384,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | spl11_16 ),
    inference(resolution,[],[f361,f75])).

fof(f361,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl11_16 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl11_16
  <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f379,plain,
    ( spl11_17
    | ~ spl11_16
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | spl11_15 ),
    inference(avatar_split_clause,[],[f374,f355,f205,f183,f109,f359,f363])).

fof(f355,plain,
    ( spl11_15
  <=> m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f374,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9
    | spl11_15 ),
    inference(subsumption_resolution,[],[f373,f111])).

fof(f373,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK2(sK0)
    | ~ spl11_6
    | ~ spl11_9
    | spl11_15 ),
    inference(subsumption_resolution,[],[f372,f184])).

fof(f372,plain,
    ( ~ v13_lattices(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK2(sK0)
    | ~ spl11_9
    | spl11_15 ),
    inference(subsumption_resolution,[],[f371,f206])).

fof(f371,plain,
    ( ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK2(sK0)
    | spl11_15 ),
    inference(resolution,[],[f357,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k5_lattices(X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f357,plain,
    ( ~ m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0))
    | spl11_15 ),
    inference(avatar_component_clause,[],[f355])).

fof(f366,plain,
    ( ~ spl11_15
    | ~ spl11_16
    | spl11_17
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f344,f205,f202,f183,f109,f363,f359,f355])).

fof(f202,plain,
    ( spl11_8
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f344,plain,
    ( k5_lattices(sK0) = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( sK2(sK0) != sK2(sK0)
    | k5_lattices(sK0) = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(superposition,[],[f342,f286])).

fof(f286,plain,
    ( ! [X0] :
        ( sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f285,f111])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f282,f206])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl11_6 ),
    inference(resolution,[],[f184,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK2(X0) = k2_lattices(X0,sK2(X0),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f342,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | k5_lattices(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f341,f111])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f340,f184])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f339,f206])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | k5_lattices(sK0) = X0 )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(resolution,[],[f314,f70])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1(sK0,X0),u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(superposition,[],[f290,f203])).

fof(f203,plain,
    ( ! [X4,X5] :
        ( k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f290,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK1(sK0,X2),X2) != X2
        | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k5_lattices(sK0) = X2 )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f289,f111])).

fof(f289,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2
        | k2_lattices(sK0,sK1(sK0,X2),X2) != X2
        | k5_lattices(sK0) = X2 )
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f284,f206])).

fof(f284,plain,
    ( ! [X2] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2
        | k2_lattices(sK0,sK1(sK0,X2),X2) != X2
        | k5_lattices(sK0) = X2 )
    | ~ spl11_6 ),
    inference(resolution,[],[f184,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k5_lattices(X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f281,plain,
    ( spl11_6
    | spl11_14
    | spl11_1
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f277,f257,f205,f202,f109,f279,f183])).

fof(f257,plain,
    ( spl11_13
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0) )
    | spl11_1
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f276,f111])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f275,f206])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(resolution,[],[f267,f74])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 )
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl11_8
    | ~ spl11_13 ),
    inference(superposition,[],[f258,f203])).

fof(f258,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 )
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl11_6
    | spl11_13
    | spl11_1
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f219,f205,f109,f257,f183])).

fof(f219,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | v13_lattices(sK0) )
    | spl11_1
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f131,f206])).

fof(f131,plain,
    ( ! [X6] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6
        | k2_lattices(sK0,sK3(sK0,X6),X6) != X6
        | v13_lattices(sK0) )
    | spl11_1 ),
    inference(resolution,[],[f111,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f248,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_12 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_12 ),
    inference(subsumption_resolution,[],[f246,f126])).

fof(f246,plain,
    ( ~ l3_lattices(sK0)
    | spl11_1
    | ~ spl11_2
    | spl11_12 ),
    inference(subsumption_resolution,[],[f245,f116])).

fof(f245,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_1
    | spl11_12 ),
    inference(subsumption_resolution,[],[f244,f111])).

fof(f244,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_12 ),
    inference(resolution,[],[f234,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f234,plain,
    ( ~ v8_lattices(sK0)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f240,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_11 ),
    inference(subsumption_resolution,[],[f238,f126])).

fof(f238,plain,
    ( ~ l3_lattices(sK0)
    | spl11_1
    | ~ spl11_2
    | spl11_11 ),
    inference(subsumption_resolution,[],[f237,f116])).

fof(f237,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_1
    | spl11_11 ),
    inference(subsumption_resolution,[],[f236,f111])).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_11 ),
    inference(resolution,[],[f230,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f230,plain,
    ( ~ v9_lattices(sK0)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f235,plain,
    ( spl11_10
    | ~ spl11_11
    | ~ spl11_12
    | spl11_1
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f214,f198,f124,f109,f232,f228,f225])).

fof(f198,plain,
    ( spl11_7
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f214,plain,
    ( ! [X2,X3] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl11_1
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f135,f199])).

fof(f199,plain,
    ( v6_lattices(sK0)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f198])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl11_1
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f129,f126])).

fof(f129,plain,
    ( ! [X2,X3] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X3)
        | ~ r3_lattices(sK0,X2,X3) )
    | spl11_1 ),
    inference(resolution,[],[f111,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f218,plain,
    ( ~ spl11_4
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl11_4
    | spl11_9 ),
    inference(subsumption_resolution,[],[f216,f126])).

fof(f216,plain,
    ( ~ l3_lattices(sK0)
    | spl11_9 ),
    inference(resolution,[],[f207,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f207,plain,
    ( ~ l1_lattices(sK0)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f213,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_7 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4
    | spl11_7 ),
    inference(subsumption_resolution,[],[f211,f126])).

fof(f211,plain,
    ( ~ l3_lattices(sK0)
    | spl11_1
    | ~ spl11_2
    | spl11_7 ),
    inference(subsumption_resolution,[],[f210,f116])).

fof(f210,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_1
    | spl11_7 ),
    inference(subsumption_resolution,[],[f209,f111])).

fof(f209,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl11_7 ),
    inference(resolution,[],[f200,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f200,plain,
    ( ~ v6_lattices(sK0)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f198])).

fof(f208,plain,
    ( ~ spl11_7
    | spl11_8
    | ~ spl11_9
    | spl11_1 ),
    inference(avatar_split_clause,[],[f130,f109,f205,f202,f198])).

fof(f130,plain,
    ( ! [X4,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4)
        | ~ v6_lattices(sK0) )
    | spl11_1 ),
    inference(resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f186,plain,
    ( ~ spl11_5
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f107,f183,f179])).

fof(f107,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f53,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f106,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f105,f51])).

fof(f51,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f49,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f127,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f122,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f117,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f51,f114])).

fof(f112,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f50,f109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13494)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (13502)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (13482)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13488)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13492)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (13492)Refutation not found, incomplete strategy% (13492)------------------------------
% 0.22/0.53  % (13492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13492)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13492)Memory used [KB]: 10746
% 0.22/0.53  % (13492)Time elapsed: 0.107 s
% 0.22/0.53  % (13492)------------------------------
% 0.22/0.53  % (13492)------------------------------
% 0.22/0.53  % (13496)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (13482)Refutation not found, incomplete strategy% (13482)------------------------------
% 0.22/0.53  % (13482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13482)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13482)Memory used [KB]: 1663
% 0.22/0.53  % (13482)Time elapsed: 0.002 s
% 0.22/0.53  % (13482)------------------------------
% 0.22/0.53  % (13482)------------------------------
% 0.22/0.53  % (13500)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (13509)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (13484)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (13487)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (13485)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (13511)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (13510)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (13507)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (13503)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (13483)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.55  % (13493)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (13498)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (13508)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.56  % (13493)Refutation not found, incomplete strategy% (13493)------------------------------
% 1.44/0.56  % (13493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (13493)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (13493)Memory used [KB]: 10746
% 1.44/0.56  % (13493)Time elapsed: 0.149 s
% 1.44/0.56  % (13493)------------------------------
% 1.44/0.56  % (13493)------------------------------
% 1.44/0.56  % (13495)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (13499)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.56  % (13501)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.56  % (13490)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (13499)Refutation not found, incomplete strategy% (13499)------------------------------
% 1.44/0.56  % (13499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (13499)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (13486)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.44/0.56  % (13499)Memory used [KB]: 10618
% 1.44/0.56  % (13499)Time elapsed: 0.159 s
% 1.44/0.56  % (13499)------------------------------
% 1.44/0.56  % (13499)------------------------------
% 1.59/0.57  % (13497)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.57  % (13502)Refutation found. Thanks to Tanya!
% 1.59/0.57  % SZS status Theorem for theBenchmark
% 1.59/0.57  % SZS output start Proof for theBenchmark
% 1.59/0.57  fof(f567,plain,(
% 1.59/0.57    $false),
% 1.59/0.57    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f186,f208,f213,f218,f235,f240,f248,f259,f281,f366,f379,f388,f422,f526,f534,f555,f566])).
% 1.59/0.57  fof(f566,plain,(
% 1.59/0.57    spl11_1 | spl11_6 | ~spl11_9 | ~spl11_20 | spl11_21),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f565])).
% 1.59/0.57  fof(f565,plain,(
% 1.59/0.57    $false | (spl11_1 | spl11_6 | ~spl11_9 | ~spl11_20 | spl11_21)),
% 1.59/0.57    inference(subsumption_resolution,[],[f564,f185])).
% 1.59/0.57  fof(f185,plain,(
% 1.59/0.57    ~v13_lattices(sK0) | spl11_6),
% 1.59/0.57    inference(avatar_component_clause,[],[f183])).
% 1.59/0.57  fof(f183,plain,(
% 1.59/0.57    spl11_6 <=> v13_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.59/0.57  fof(f564,plain,(
% 1.59/0.57    v13_lattices(sK0) | (spl11_1 | ~spl11_9 | ~spl11_20 | spl11_21)),
% 1.59/0.57    inference(subsumption_resolution,[],[f563,f111])).
% 1.59/0.57  fof(f111,plain,(
% 1.59/0.57    ~v2_struct_0(sK0) | spl11_1),
% 1.59/0.57    inference(avatar_component_clause,[],[f109])).
% 1.59/0.57  fof(f109,plain,(
% 1.59/0.57    spl11_1 <=> v2_struct_0(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.59/0.57  fof(f563,plain,(
% 1.59/0.57    v2_struct_0(sK0) | v13_lattices(sK0) | (~spl11_9 | ~spl11_20 | spl11_21)),
% 1.59/0.57    inference(subsumption_resolution,[],[f562,f524])).
% 1.59/0.57  fof(f524,plain,(
% 1.59/0.57    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl11_20),
% 1.59/0.57    inference(avatar_component_clause,[],[f523])).
% 1.59/0.57  fof(f523,plain,(
% 1.59/0.57    spl11_20 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.59/0.57  fof(f562,plain,(
% 1.59/0.57    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | (~spl11_9 | spl11_21)),
% 1.59/0.57    inference(subsumption_resolution,[],[f561,f206])).
% 1.59/0.57  fof(f206,plain,(
% 1.59/0.57    l1_lattices(sK0) | ~spl11_9),
% 1.59/0.57    inference(avatar_component_clause,[],[f205])).
% 1.59/0.57  fof(f205,plain,(
% 1.59/0.57    spl11_9 <=> l1_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.59/0.57  fof(f561,plain,(
% 1.59/0.57    ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | spl11_21),
% 1.59/0.57    inference(resolution,[],[f554,f74])).
% 1.59/0.57  fof(f74,plain,(
% 1.59/0.57    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f32,plain,(
% 1.59/0.57    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f31])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f12])).
% 1.59/0.57  fof(f12,axiom,(
% 1.59/0.57    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 1.59/0.57  fof(f554,plain,(
% 1.59/0.57    ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | spl11_21),
% 1.59/0.57    inference(avatar_component_clause,[],[f552])).
% 1.59/0.57  fof(f552,plain,(
% 1.59/0.57    spl11_21 <=> m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.59/0.57  fof(f555,plain,(
% 1.59/0.57    ~spl11_21 | spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_14 | ~spl11_20),
% 1.59/0.57    inference(avatar_split_clause,[],[f543,f523,f279,f232,f228,f225,f124,f119,f114,f109,f552])).
% 1.59/0.57  fof(f114,plain,(
% 1.59/0.57    spl11_2 <=> v10_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.59/0.57  fof(f119,plain,(
% 1.59/0.57    spl11_3 <=> v4_lattice3(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.59/0.57  fof(f124,plain,(
% 1.59/0.57    spl11_4 <=> l3_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.59/0.57  fof(f225,plain,(
% 1.59/0.57    spl11_10 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X2,X3) | r1_lattices(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.59/0.57  fof(f228,plain,(
% 1.59/0.57    spl11_11 <=> v9_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.59/0.57  fof(f232,plain,(
% 1.59/0.57    spl11_12 <=> v8_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.59/0.57  fof(f279,plain,(
% 1.59/0.57    spl11_14 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 1.59/0.57  fof(f543,plain,(
% 1.59/0.57    ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_14 | ~spl11_20)),
% 1.59/0.57    inference(subsumption_resolution,[],[f542,f524])).
% 1.59/0.57  fof(f542,plain,(
% 1.59/0.57    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_14)),
% 1.59/0.57    inference(trivial_inequality_removal,[],[f541])).
% 1.59/0.57  fof(f541,plain,(
% 1.59/0.57    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_14)),
% 1.59/0.57    inference(superposition,[],[f280,f497])).
% 1.59/0.57  fof(f497,plain,(
% 1.59/0.57    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(resolution,[],[f479,f54])).
% 1.59/0.57  fof(f54,plain,(
% 1.59/0.57    v1_xboole_0(k1_xboole_0)),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    v1_xboole_0(k1_xboole_0)),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.59/0.57  fof(f479,plain,(
% 1.59/0.57    ( ! [X12,X11] : (~v1_xboole_0(X11) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),X12)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(resolution,[],[f428,f88])).
% 1.59/0.57  fof(f88,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.59/0.57  fof(f428,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f427,f111])).
% 1.59/0.57  fof(f427,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f423,f126])).
% 1.59/0.57  fof(f126,plain,(
% 1.59/0.57    l3_lattices(sK0) | ~spl11_4),
% 1.59/0.57    inference(avatar_component_clause,[],[f124])).
% 1.59/0.57  fof(f423,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | r2_hidden(sK6(sK0,X1,k6_domain_1(u1_struct_0(sK0),X0)),X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(resolution,[],[f323,f89])).
% 1.59/0.57  fof(f89,plain,(
% 1.59/0.57    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f42])).
% 1.59/0.57  fof(f42,plain,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f41])).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f14])).
% 1.59/0.57  fof(f14,axiom,(
% 1.59/0.57    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.59/0.57  fof(f323,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | r2_hidden(sK6(sK0,X0,k6_domain_1(u1_struct_0(sK0),X1)),X0)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f320])).
% 1.59/0.57  fof(f320,plain,(
% 1.59/0.57    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,k6_domain_1(u1_struct_0(sK0),X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(resolution,[],[f192,f254])).
% 1.59/0.57  fof(f254,plain,(
% 1.59/0.57    ( ! [X2,X3] : (~r3_lattices(sK0,X3,X2) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f253])).
% 1.59/0.57  fof(f253,plain,(
% 1.59/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_4 | ~spl11_10 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(resolution,[],[f250,f226])).
% 1.59/0.57  fof(f226,plain,(
% 1.59/0.57    ( ! [X2,X3] : (r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl11_10),
% 1.59/0.57    inference(avatar_component_clause,[],[f225])).
% 1.59/0.57  fof(f250,plain,(
% 1.59/0.57    ( ! [X10,X9] : (~r1_lattices(sK0,X9,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~m1_subset_1(X9,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_4 | ~spl11_11 | ~spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f242,f233])).
% 1.59/0.57  fof(f233,plain,(
% 1.59/0.57    v8_lattices(sK0) | ~spl11_12),
% 1.59/0.57    inference(avatar_component_clause,[],[f232])).
% 1.59/0.57  fof(f242,plain,(
% 1.59/0.57    ( ! [X10,X9] : (~v8_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | (spl11_1 | ~spl11_4 | ~spl11_11)),
% 1.59/0.57    inference(subsumption_resolution,[],[f137,f229])).
% 1.59/0.57  fof(f229,plain,(
% 1.59/0.57    v9_lattices(sK0) | ~spl11_11),
% 1.59/0.57    inference(avatar_component_clause,[],[f228])).
% 1.59/0.57  fof(f137,plain,(
% 1.59/0.57    ( ! [X10,X9] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | (spl11_1 | ~spl11_4)),
% 1.59/0.57    inference(subsumption_resolution,[],[f133,f126])).
% 1.59/0.57  fof(f133,plain,(
% 1.59/0.57    ( ! [X10,X9] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,X9,X10) = X9 | ~r1_lattices(sK0,X9,X10)) ) | spl11_1),
% 1.59/0.57    inference(resolution,[],[f111,f66])).
% 1.59/0.57  fof(f66,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f28])).
% 1.59/0.57  fof(f28,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f27])).
% 1.59/0.57  fof(f27,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f11])).
% 1.59/0.57  fof(f11,axiom,(
% 1.59/0.57    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.59/0.57  fof(f192,plain,(
% 1.59/0.57    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),X2) | r2_hidden(sK6(sK0,X3,k6_domain_1(u1_struct_0(sK0),X2)),X3) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4)),
% 1.59/0.57    inference(superposition,[],[f165,f156])).
% 1.59/0.57  fof(f156,plain,(
% 1.59/0.57    ( ! [X2] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4)),
% 1.59/0.57    inference(subsumption_resolution,[],[f155,f126])).
% 1.59/0.57  fof(f155,plain,(
% 1.59/0.57    ( ! [X2] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | (spl11_1 | ~spl11_2 | ~spl11_3)),
% 1.59/0.57    inference(subsumption_resolution,[],[f154,f111])).
% 1.59/0.57  fof(f154,plain,(
% 1.59/0.57    ( ! [X2] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | (~spl11_2 | ~spl11_3)),
% 1.59/0.57    inference(subsumption_resolution,[],[f140,f116])).
% 1.59/0.57  fof(f116,plain,(
% 1.59/0.57    v10_lattices(sK0) | ~spl11_2),
% 1.59/0.57    inference(avatar_component_clause,[],[f114])).
% 1.59/0.57  fof(f140,plain,(
% 1.59/0.57    ( ! [X2] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = X2) ) | ~spl11_3),
% 1.59/0.57    inference(resolution,[],[f121,f82])).
% 1.59/0.57  fof(f82,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) )),
% 1.59/0.57    inference(cnf_transformation,[],[f38])).
% 1.59/0.57  fof(f38,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f37])).
% 1.59/0.57  fof(f37,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f16])).
% 1.59/0.57  fof(f16,axiom,(
% 1.59/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).
% 1.59/0.57  fof(f121,plain,(
% 1.59/0.57    v4_lattice3(sK0) | ~spl11_3),
% 1.59/0.57    inference(avatar_component_clause,[],[f119])).
% 1.59/0.57  fof(f165,plain,(
% 1.59/0.57    ( ! [X8,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8)) | r2_hidden(sK6(sK0,X7,X8),X7)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4)),
% 1.59/0.57    inference(subsumption_resolution,[],[f164,f126])).
% 1.59/0.57  fof(f164,plain,(
% 1.59/0.57    ( ! [X8,X7] : (~l3_lattices(sK0) | r2_hidden(sK6(sK0,X7,X8),X7) | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8))) ) | (spl11_1 | ~spl11_2 | ~spl11_3)),
% 1.59/0.57    inference(subsumption_resolution,[],[f163,f111])).
% 1.59/0.57  fof(f163,plain,(
% 1.59/0.57    ( ! [X8,X7] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | r2_hidden(sK6(sK0,X7,X8),X7) | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8))) ) | (~spl11_2 | ~spl11_3)),
% 1.59/0.57    inference(subsumption_resolution,[],[f143,f116])).
% 1.59/0.57  fof(f143,plain,(
% 1.59/0.57    ( ! [X8,X7] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | r2_hidden(sK6(sK0,X7,X8),X7) | r3_lattices(sK0,k15_lattice3(sK0,X7),k15_lattice3(sK0,X8))) ) | ~spl11_3),
% 1.59/0.57    inference(resolution,[],[f121,f86])).
% 1.59/0.57  fof(f86,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | r2_hidden(sK6(X0,X1,X2),X1) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) )),
% 1.59/0.57    inference(cnf_transformation,[],[f40])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f39])).
% 1.59/0.57  fof(f39,plain,(
% 1.59/0.57    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f18])).
% 1.59/0.57  fof(f18,axiom,(
% 1.59/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 1.59/0.57  fof(f280,plain,(
% 1.59/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl11_14),
% 1.59/0.57    inference(avatar_component_clause,[],[f279])).
% 1.59/0.57  fof(f534,plain,(
% 1.59/0.57    spl11_1 | ~spl11_4 | spl11_20),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f533])).
% 1.59/0.57  fof(f533,plain,(
% 1.59/0.57    $false | (spl11_1 | ~spl11_4 | spl11_20)),
% 1.59/0.57    inference(subsumption_resolution,[],[f532,f111])).
% 1.59/0.57  fof(f532,plain,(
% 1.59/0.57    v2_struct_0(sK0) | (~spl11_4 | spl11_20)),
% 1.59/0.57    inference(subsumption_resolution,[],[f531,f126])).
% 1.59/0.57  fof(f531,plain,(
% 1.59/0.57    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl11_20),
% 1.59/0.57    inference(resolution,[],[f525,f89])).
% 1.59/0.57  fof(f525,plain,(
% 1.59/0.57    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl11_20),
% 1.59/0.57    inference(avatar_component_clause,[],[f523])).
% 1.59/0.57  fof(f526,plain,(
% 1.59/0.57    ~spl11_20 | spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_6 | ~spl11_9 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_17 | ~spl11_18),
% 1.59/0.57    inference(avatar_split_clause,[],[f517,f419,f363,f232,f228,f225,f205,f183,f179,f124,f119,f114,f109,f523])).
% 1.59/0.57  fof(f179,plain,(
% 1.59/0.57    spl11_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.59/0.57  fof(f363,plain,(
% 1.59/0.57    spl11_17 <=> k5_lattices(sK0) = sK2(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.59/0.57  fof(f419,plain,(
% 1.59/0.57    spl11_18 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.59/0.57  fof(f517,plain,(
% 1.59/0.57    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_6 | ~spl11_9 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_17 | ~spl11_18)),
% 1.59/0.57    inference(subsumption_resolution,[],[f516,f421])).
% 1.59/0.57  fof(f421,plain,(
% 1.59/0.57    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl11_18),
% 1.59/0.57    inference(avatar_component_clause,[],[f419])).
% 1.59/0.57  fof(f516,plain,(
% 1.59/0.57    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_6 | ~spl11_9 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_17)),
% 1.59/0.57    inference(subsumption_resolution,[],[f506,f181])).
% 1.59/0.57  fof(f181,plain,(
% 1.59/0.57    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl11_5),
% 1.59/0.57    inference(avatar_component_clause,[],[f179])).
% 1.59/0.57  fof(f506,plain,(
% 1.59/0.57    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_6 | ~spl11_9 | ~spl11_10 | ~spl11_11 | ~spl11_12 | ~spl11_17)),
% 1.59/0.57    inference(superposition,[],[f497,f390])).
% 1.59/0.57  fof(f390,plain,(
% 1.59/0.57    ( ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_6 | ~spl11_9 | ~spl11_17)),
% 1.59/0.57    inference(backward_demodulation,[],[f288,f365])).
% 1.59/0.57  fof(f365,plain,(
% 1.59/0.57    k5_lattices(sK0) = sK2(sK0) | ~spl11_17),
% 1.59/0.57    inference(avatar_component_clause,[],[f363])).
% 1.59/0.57  fof(f288,plain,(
% 1.59/0.57    ( ! [X1] : (sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f287,f111])).
% 1.59/0.57  fof(f287,plain,(
% 1.59/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0)) | v2_struct_0(sK0)) ) | (~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f283,f206])).
% 1.59/0.57  fof(f283,plain,(
% 1.59/0.57    ( ! [X1] : (~l1_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,X1,sK2(sK0)) | v2_struct_0(sK0)) ) | ~spl11_6),
% 1.59/0.57    inference(resolution,[],[f184,f72])).
% 1.59/0.57  fof(f72,plain,(
% 1.59/0.57    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK2(X0) = k2_lattices(X0,X2,sK2(X0)) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f184,plain,(
% 1.59/0.57    v13_lattices(sK0) | ~spl11_6),
% 1.59/0.57    inference(avatar_component_clause,[],[f183])).
% 1.59/0.57  fof(f422,plain,(
% 1.59/0.57    spl11_18 | spl11_1 | ~spl11_6 | ~spl11_9 | ~spl11_17),
% 1.59/0.57    inference(avatar_split_clause,[],[f415,f363,f205,f183,f109,f419])).
% 1.59/0.57  fof(f415,plain,(
% 1.59/0.57    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl11_1 | ~spl11_6 | ~spl11_9 | ~spl11_17)),
% 1.59/0.57    inference(subsumption_resolution,[],[f414,f184])).
% 1.59/0.57  fof(f414,plain,(
% 1.59/0.57    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | (spl11_1 | ~spl11_9 | ~spl11_17)),
% 1.59/0.57    inference(subsumption_resolution,[],[f413,f111])).
% 1.59/0.57  fof(f413,plain,(
% 1.59/0.57    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v13_lattices(sK0) | (~spl11_9 | ~spl11_17)),
% 1.59/0.57    inference(subsumption_resolution,[],[f412,f206])).
% 1.59/0.57  fof(f412,plain,(
% 1.59/0.57    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~v13_lattices(sK0) | ~spl11_17),
% 1.59/0.57    inference(superposition,[],[f75,f365])).
% 1.59/0.57  fof(f75,plain,(
% 1.59/0.57    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f388,plain,(
% 1.59/0.57    spl11_1 | ~spl11_6 | ~spl11_9 | spl11_16),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f387])).
% 1.59/0.57  fof(f387,plain,(
% 1.59/0.57    $false | (spl11_1 | ~spl11_6 | ~spl11_9 | spl11_16)),
% 1.59/0.57    inference(subsumption_resolution,[],[f386,f184])).
% 1.59/0.57  fof(f386,plain,(
% 1.59/0.57    ~v13_lattices(sK0) | (spl11_1 | ~spl11_9 | spl11_16)),
% 1.59/0.57    inference(subsumption_resolution,[],[f385,f111])).
% 1.59/0.57  fof(f385,plain,(
% 1.59/0.57    v2_struct_0(sK0) | ~v13_lattices(sK0) | (~spl11_9 | spl11_16)),
% 1.59/0.57    inference(subsumption_resolution,[],[f384,f206])).
% 1.59/0.57  fof(f384,plain,(
% 1.59/0.57    ~l1_lattices(sK0) | v2_struct_0(sK0) | ~v13_lattices(sK0) | spl11_16),
% 1.59/0.57    inference(resolution,[],[f361,f75])).
% 1.59/0.57  fof(f361,plain,(
% 1.59/0.57    ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | spl11_16),
% 1.59/0.57    inference(avatar_component_clause,[],[f359])).
% 1.59/0.57  fof(f359,plain,(
% 1.59/0.57    spl11_16 <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 1.59/0.57  fof(f379,plain,(
% 1.59/0.57    spl11_17 | ~spl11_16 | spl11_1 | ~spl11_6 | ~spl11_9 | spl11_15),
% 1.59/0.57    inference(avatar_split_clause,[],[f374,f355,f205,f183,f109,f359,f363])).
% 1.59/0.57  fof(f355,plain,(
% 1.59/0.57    spl11_15 <=> m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.59/0.57  fof(f374,plain,(
% 1.59/0.57    ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = sK2(sK0) | (spl11_1 | ~spl11_6 | ~spl11_9 | spl11_15)),
% 1.59/0.57    inference(subsumption_resolution,[],[f373,f111])).
% 1.59/0.57  fof(f373,plain,(
% 1.59/0.57    ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = sK2(sK0) | (~spl11_6 | ~spl11_9 | spl11_15)),
% 1.59/0.57    inference(subsumption_resolution,[],[f372,f184])).
% 1.59/0.57  fof(f372,plain,(
% 1.59/0.57    ~v13_lattices(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = sK2(sK0) | (~spl11_9 | spl11_15)),
% 1.59/0.57    inference(subsumption_resolution,[],[f371,f206])).
% 1.59/0.57  fof(f371,plain,(
% 1.59/0.57    ~l1_lattices(sK0) | ~v13_lattices(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = sK2(sK0) | spl11_15),
% 1.59/0.57    inference(resolution,[],[f357,f70])).
% 1.59/0.57  fof(f70,plain,(
% 1.59/0.57    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | k5_lattices(X0) = X1) )),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f29])).
% 1.59/0.57  fof(f29,plain,(
% 1.59/0.57    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,axiom,(
% 1.59/0.57    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 1.59/0.57  fof(f357,plain,(
% 1.59/0.57    ~m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0)) | spl11_15),
% 1.59/0.57    inference(avatar_component_clause,[],[f355])).
% 1.59/0.57  fof(f366,plain,(
% 1.59/0.57    ~spl11_15 | ~spl11_16 | spl11_17 | spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9),
% 1.59/0.57    inference(avatar_split_clause,[],[f344,f205,f202,f183,f109,f363,f359,f355])).
% 1.59/0.57  fof(f202,plain,(
% 1.59/0.57    spl11_8 <=> ! [X5,X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)))),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.59/0.57  fof(f344,plain,(
% 1.59/0.57    k5_lattices(sK0) = sK2(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0)) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(trivial_inequality_removal,[],[f343])).
% 1.59/0.57  fof(f343,plain,(
% 1.59/0.57    sK2(sK0) != sK2(sK0) | k5_lattices(sK0) = sK2(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1(sK0,sK2(sK0)),u1_struct_0(sK0)) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(superposition,[],[f342,f286])).
% 1.59/0.57  fof(f286,plain,(
% 1.59/0.57    ( ! [X0] : (sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f285,f111])).
% 1.59/0.57  fof(f285,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0) | v2_struct_0(sK0)) ) | (~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f282,f206])).
% 1.59/0.57  fof(f282,plain,(
% 1.59/0.57    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2(sK0) = k2_lattices(sK0,sK2(sK0),X0) | v2_struct_0(sK0)) ) | ~spl11_6),
% 1.59/0.57    inference(resolution,[],[f184,f71])).
% 1.59/0.57  fof(f71,plain,(
% 1.59/0.57    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK2(X0) = k2_lattices(X0,sK2(X0),X2) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f342,plain,(
% 1.59/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | k5_lattices(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f341,f111])).
% 1.59/0.57  fof(f341,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f340,f184])).
% 1.59/0.57  fof(f340,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f339,f206])).
% 1.59/0.57  fof(f339,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~l1_lattices(sK0) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f338])).
% 1.59/0.57  fof(f338,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~l1_lattices(sK0) | ~v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = X0) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(resolution,[],[f314,f70])).
% 1.59/0.57  fof(f314,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f309])).
% 1.59/0.57  fof(f309,plain,(
% 1.59/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1(sK0,X0),u1_struct_0(sK0))) ) | (spl11_1 | ~spl11_6 | ~spl11_8 | ~spl11_9)),
% 1.59/0.57    inference(superposition,[],[f290,f203])).
% 1.59/0.57  fof(f203,plain,(
% 1.59/0.57    ( ! [X4,X5] : (k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | ~spl11_8),
% 1.59/0.57    inference(avatar_component_clause,[],[f202])).
% 1.59/0.57  fof(f290,plain,(
% 1.59/0.57    ( ! [X2] : (k2_lattices(sK0,sK1(sK0,X2),X2) != X2 | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | k5_lattices(sK0) = X2) ) | (spl11_1 | ~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f289,f111])).
% 1.59/0.57  fof(f289,plain,(
% 1.59/0.57    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2 | k2_lattices(sK0,sK1(sK0,X2),X2) != X2 | k5_lattices(sK0) = X2) ) | (~spl11_6 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f284,f206])).
% 1.59/0.57  fof(f284,plain,(
% 1.59/0.57    ( ! [X2] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,sK1(sK0,X2)) != X2 | k2_lattices(sK0,sK1(sK0,X2),X2) != X2 | k5_lattices(sK0) = X2) ) | ~spl11_6),
% 1.59/0.57    inference(resolution,[],[f184,f67])).
% 1.59/0.57  fof(f67,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k5_lattices(X0) = X1) )),
% 1.59/0.57    inference(cnf_transformation,[],[f30])).
% 1.59/0.57  fof(f281,plain,(
% 1.59/0.57    spl11_6 | spl11_14 | spl11_1 | ~spl11_8 | ~spl11_9 | ~spl11_13),
% 1.59/0.57    inference(avatar_split_clause,[],[f277,f257,f205,f202,f109,f279,f183])).
% 1.59/0.57  fof(f257,plain,(
% 1.59/0.57    spl11_13 <=> ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.59/0.57  fof(f277,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0)) ) | (spl11_1 | ~spl11_8 | ~spl11_9 | ~spl11_13)),
% 1.59/0.57    inference(subsumption_resolution,[],[f276,f111])).
% 1.59/0.57  fof(f276,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl11_8 | ~spl11_9 | ~spl11_13)),
% 1.59/0.57    inference(subsumption_resolution,[],[f275,f206])).
% 1.59/0.57  fof(f275,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl11_8 | ~spl11_13)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f274])).
% 1.59/0.57  fof(f274,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (~spl11_8 | ~spl11_13)),
% 1.59/0.57    inference(resolution,[],[f267,f74])).
% 1.59/0.57  fof(f267,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0) ) | (~spl11_8 | ~spl11_13)),
% 1.59/0.57    inference(duplicate_literal_removal,[],[f264])).
% 1.59/0.57  fof(f264,plain,(
% 1.59/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))) ) | (~spl11_8 | ~spl11_13)),
% 1.59/0.57    inference(superposition,[],[f258,f203])).
% 1.59/0.57  fof(f258,plain,(
% 1.59/0.57    ( ! [X6] : (k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6) ) | ~spl11_13),
% 1.59/0.57    inference(avatar_component_clause,[],[f257])).
% 1.59/0.57  fof(f259,plain,(
% 1.59/0.57    spl11_6 | spl11_13 | spl11_1 | ~spl11_9),
% 1.59/0.57    inference(avatar_split_clause,[],[f219,f205,f109,f257,f183])).
% 1.59/0.57  fof(f219,plain,(
% 1.59/0.57    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | v13_lattices(sK0)) ) | (spl11_1 | ~spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f131,f206])).
% 1.59/0.57  fof(f131,plain,(
% 1.59/0.57    ( ! [X6] : (~l1_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,sK3(sK0,X6)) != X6 | k2_lattices(sK0,sK3(sK0,X6),X6) != X6 | v13_lattices(sK0)) ) | spl11_1),
% 1.59/0.57    inference(resolution,[],[f111,f73])).
% 1.59/0.57  fof(f73,plain,(
% 1.59/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | k2_lattices(X0,sK3(X0,X1),X1) != X1 | v13_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f32])).
% 1.59/0.57  fof(f248,plain,(
% 1.59/0.57    spl11_1 | ~spl11_2 | ~spl11_4 | spl11_12),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f247])).
% 1.59/0.57  fof(f247,plain,(
% 1.59/0.57    $false | (spl11_1 | ~spl11_2 | ~spl11_4 | spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f246,f126])).
% 1.59/0.57  fof(f246,plain,(
% 1.59/0.57    ~l3_lattices(sK0) | (spl11_1 | ~spl11_2 | spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f245,f116])).
% 1.59/0.57  fof(f245,plain,(
% 1.59/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl11_1 | spl11_12)),
% 1.59/0.57    inference(subsumption_resolution,[],[f244,f111])).
% 1.59/0.57  fof(f244,plain,(
% 1.59/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl11_12),
% 1.59/0.57    inference(resolution,[],[f234,f62])).
% 1.59/0.57  fof(f62,plain,(
% 1.59/0.57    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f25,plain,(
% 1.59/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.59/0.57    inference(flattening,[],[f24])).
% 1.59/0.57  fof(f24,plain,(
% 1.59/0.57    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.59/0.57    inference(ennf_transformation,[],[f7])).
% 1.59/0.57  fof(f7,axiom,(
% 1.59/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.59/0.57  fof(f234,plain,(
% 1.59/0.57    ~v8_lattices(sK0) | spl11_12),
% 1.59/0.57    inference(avatar_component_clause,[],[f232])).
% 1.59/0.57  fof(f240,plain,(
% 1.59/0.57    spl11_1 | ~spl11_2 | ~spl11_4 | spl11_11),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f239])).
% 1.59/0.57  fof(f239,plain,(
% 1.59/0.57    $false | (spl11_1 | ~spl11_2 | ~spl11_4 | spl11_11)),
% 1.59/0.57    inference(subsumption_resolution,[],[f238,f126])).
% 1.59/0.57  fof(f238,plain,(
% 1.59/0.57    ~l3_lattices(sK0) | (spl11_1 | ~spl11_2 | spl11_11)),
% 1.59/0.57    inference(subsumption_resolution,[],[f237,f116])).
% 1.59/0.57  fof(f237,plain,(
% 1.59/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl11_1 | spl11_11)),
% 1.59/0.57    inference(subsumption_resolution,[],[f236,f111])).
% 1.59/0.57  fof(f236,plain,(
% 1.59/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl11_11),
% 1.59/0.57    inference(resolution,[],[f230,f63])).
% 1.59/0.57  fof(f63,plain,(
% 1.59/0.57    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f230,plain,(
% 1.59/0.57    ~v9_lattices(sK0) | spl11_11),
% 1.59/0.57    inference(avatar_component_clause,[],[f228])).
% 1.59/0.57  fof(f235,plain,(
% 1.59/0.57    spl11_10 | ~spl11_11 | ~spl11_12 | spl11_1 | ~spl11_4 | ~spl11_7),
% 1.59/0.57    inference(avatar_split_clause,[],[f214,f198,f124,f109,f232,f228,f225])).
% 1.59/0.57  fof(f198,plain,(
% 1.59/0.57    spl11_7 <=> v6_lattices(sK0)),
% 1.59/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.59/0.57  fof(f214,plain,(
% 1.59/0.57    ( ! [X2,X3] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | (spl11_1 | ~spl11_4 | ~spl11_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f135,f199])).
% 1.59/0.57  fof(f199,plain,(
% 1.59/0.57    v6_lattices(sK0) | ~spl11_7),
% 1.59/0.57    inference(avatar_component_clause,[],[f198])).
% 1.59/0.57  fof(f135,plain,(
% 1.59/0.57    ( ! [X2,X3] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | (spl11_1 | ~spl11_4)),
% 1.59/0.57    inference(subsumption_resolution,[],[f129,f126])).
% 1.59/0.57  fof(f129,plain,(
% 1.59/0.57    ( ! [X2,X3] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X3) | ~r3_lattices(sK0,X2,X3)) ) | spl11_1),
% 1.59/0.57    inference(resolution,[],[f111,f95])).
% 1.59/0.57  fof(f95,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f46])).
% 1.59/0.57  fof(f46,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f45])).
% 1.59/0.57  fof(f45,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.59/0.57  fof(f218,plain,(
% 1.59/0.57    ~spl11_4 | spl11_9),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f217])).
% 1.59/0.57  fof(f217,plain,(
% 1.59/0.57    $false | (~spl11_4 | spl11_9)),
% 1.59/0.57    inference(subsumption_resolution,[],[f216,f126])).
% 1.59/0.57  fof(f216,plain,(
% 1.59/0.57    ~l3_lattices(sK0) | spl11_9),
% 1.59/0.57    inference(resolution,[],[f207,f56])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.59/0.57    inference(ennf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,axiom,(
% 1.59/0.57    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.59/0.57  fof(f207,plain,(
% 1.59/0.57    ~l1_lattices(sK0) | spl11_9),
% 1.59/0.57    inference(avatar_component_clause,[],[f205])).
% 1.59/0.57  fof(f213,plain,(
% 1.59/0.57    spl11_1 | ~spl11_2 | ~spl11_4 | spl11_7),
% 1.59/0.57    inference(avatar_contradiction_clause,[],[f212])).
% 1.59/0.57  fof(f212,plain,(
% 1.59/0.57    $false | (spl11_1 | ~spl11_2 | ~spl11_4 | spl11_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f211,f126])).
% 1.59/0.57  fof(f211,plain,(
% 1.59/0.57    ~l3_lattices(sK0) | (spl11_1 | ~spl11_2 | spl11_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f210,f116])).
% 1.59/0.57  fof(f210,plain,(
% 1.59/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl11_1 | spl11_7)),
% 1.59/0.57    inference(subsumption_resolution,[],[f209,f111])).
% 1.59/0.57  fof(f209,plain,(
% 1.59/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl11_7),
% 1.59/0.57    inference(resolution,[],[f200,f60])).
% 1.59/0.57  fof(f60,plain,(
% 1.59/0.57    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f25])).
% 1.59/0.57  fof(f200,plain,(
% 1.59/0.57    ~v6_lattices(sK0) | spl11_7),
% 1.59/0.57    inference(avatar_component_clause,[],[f198])).
% 1.59/0.57  fof(f208,plain,(
% 1.59/0.57    ~spl11_7 | spl11_8 | ~spl11_9 | spl11_1),
% 1.59/0.57    inference(avatar_split_clause,[],[f130,f109,f205,f202,f198])).
% 1.59/0.57  fof(f130,plain,(
% 1.59/0.57    ( ! [X4,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X5) = k2_lattices(sK0,X5,X4) | ~v6_lattices(sK0)) ) | spl11_1),
% 1.59/0.57    inference(resolution,[],[f111,f78])).
% 1.59/0.57  fof(f78,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f34])).
% 1.59/0.57  fof(f34,plain,(
% 1.59/0.57    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f33])).
% 1.59/0.57  fof(f33,plain,(
% 1.59/0.57    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f13])).
% 1.59/0.57  fof(f13,axiom,(
% 1.59/0.57    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 1.59/0.57  fof(f186,plain,(
% 1.59/0.57    ~spl11_5 | ~spl11_6),
% 1.59/0.57    inference(avatar_split_clause,[],[f107,f183,f179])).
% 1.59/0.57  fof(f107,plain,(
% 1.59/0.57    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f106,f53])).
% 1.59/0.57  fof(f53,plain,(
% 1.59/0.57    l3_lattices(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f22,plain,(
% 1.59/0.57    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.59/0.57    inference(flattening,[],[f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f20])).
% 1.59/0.57  fof(f20,negated_conjecture,(
% 1.59/0.57    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.59/0.57    inference(negated_conjecture,[],[f19])).
% 1.59/0.57  fof(f19,conjecture,(
% 1.59/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 1.59/0.57  fof(f106,plain,(
% 1.59/0.57    ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f105,f51])).
% 1.59/0.57  fof(f51,plain,(
% 1.59/0.57    v10_lattices(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f105,plain,(
% 1.59/0.57    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f49,f50])).
% 1.59/0.57  fof(f50,plain,(
% 1.59/0.57    ~v2_struct_0(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f49,plain,(
% 1.59/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f127,plain,(
% 1.59/0.57    spl11_4),
% 1.59/0.57    inference(avatar_split_clause,[],[f53,f124])).
% 1.59/0.57  fof(f122,plain,(
% 1.59/0.57    spl11_3),
% 1.59/0.57    inference(avatar_split_clause,[],[f52,f119])).
% 1.59/0.57  fof(f52,plain,(
% 1.59/0.57    v4_lattice3(sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f22])).
% 1.59/0.57  fof(f117,plain,(
% 1.59/0.57    spl11_2),
% 1.59/0.57    inference(avatar_split_clause,[],[f51,f114])).
% 1.59/0.57  fof(f112,plain,(
% 1.59/0.57    ~spl11_1),
% 1.59/0.57    inference(avatar_split_clause,[],[f50,f109])).
% 1.59/0.57  % SZS output end Proof for theBenchmark
% 1.59/0.57  % (13502)------------------------------
% 1.59/0.57  % (13502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (13502)Termination reason: Refutation
% 1.59/0.57  
% 1.59/0.57  % (13502)Memory used [KB]: 11257
% 1.59/0.57  % (13502)Time elapsed: 0.131 s
% 1.59/0.57  % (13502)------------------------------
% 1.59/0.57  % (13502)------------------------------
% 1.59/0.57  % (13491)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.57  % (13505)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.57  % (13481)Success in time 0.206 s
%------------------------------------------------------------------------------
