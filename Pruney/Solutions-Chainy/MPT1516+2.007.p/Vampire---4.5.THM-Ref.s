%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:48 EST 2020

% Result     : Theorem 6.95s
% Output     : Refutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  432 (1000 expanded)
%              Number of leaves         :   81 ( 428 expanded)
%              Depth                    :   17
%              Number of atoms          : 2200 (4411 expanded)
%              Number of equality atoms :  345 ( 537 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f201,f206,f211,f216,f232,f244,f252,f327,f334,f342,f389,f429,f482,f486,f494,f591,f599,f652,f766,f809,f850,f1016,f1184,f1189,f1225,f1277,f1287,f1409,f1453,f1757,f1773,f1996,f2438,f2461,f2475,f2755,f2770,f2780,f3273,f4642,f4662,f5222,f5239,f5524,f6437,f7185,f7641,f7660,f10175,f10945,f11310,f11333,f11357])).

fof(f11357,plain,
    ( spl18_1
    | spl18_5
    | ~ spl18_11
    | ~ spl18_386
    | ~ spl18_463
    | ~ spl18_520 ),
    inference(avatar_contradiction_clause,[],[f11356])).

fof(f11356,plain,
    ( $false
    | spl18_1
    | spl18_5
    | ~ spl18_11
    | ~ spl18_386
    | ~ spl18_463
    | ~ spl18_520 ),
    inference(subsumption_resolution,[],[f11355,f200])).

fof(f200,plain,
    ( ~ v2_struct_0(sK0)
    | spl18_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl18_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f11355,plain,
    ( v2_struct_0(sK0)
    | spl18_5
    | ~ spl18_11
    | ~ spl18_386
    | ~ spl18_463
    | ~ spl18_520 ),
    inference(subsumption_resolution,[],[f11354,f321])).

fof(f321,plain,
    ( l1_lattices(sK0)
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl18_11
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f11354,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl18_5
    | ~ spl18_386
    | ~ spl18_463
    | ~ spl18_520 ),
    inference(subsumption_resolution,[],[f11353,f7659])).

fof(f7659,plain,
    ( ! [X3] : m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
    | ~ spl18_386 ),
    inference(avatar_component_clause,[],[f7658])).

fof(f7658,plain,
    ( spl18_386
  <=> ! [X3] : m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_386])])).

fof(f11353,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl18_5
    | ~ spl18_463
    | ~ spl18_520 ),
    inference(subsumption_resolution,[],[f11352,f10174])).

fof(f10174,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))
    | ~ spl18_463 ),
    inference(avatar_component_clause,[],[f10173])).

fof(f10173,plain,
    ( spl18_463
  <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_463])])).

fof(f11352,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl18_5
    | ~ spl18_520 ),
    inference(subsumption_resolution,[],[f11350,f227])).

fof(f227,plain,
    ( ~ v13_lattices(sK0)
    | spl18_5 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl18_5
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f11350,plain,
    ( v13_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_520 ),
    inference(trivial_inequality_removal,[],[f11349])).

fof(f11349,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | v13_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_520 ),
    inference(superposition,[],[f136,f11332])).

fof(f11332,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl18_520 ),
    inference(avatar_component_clause,[],[f11331])).

fof(f11331,plain,
    ( spl18_520
  <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_520])])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f11333,plain,
    ( spl18_520
    | ~ spl18_120
    | ~ spl18_517 ),
    inference(avatar_split_clause,[],[f11314,f11305,f1755,f11331])).

fof(f1755,plain,
    ( spl18_120
  <=> ! [X5] : sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_120])])).

fof(f11305,plain,
    ( spl18_517
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_517])])).

fof(f11314,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl18_120
    | ~ spl18_517 ),
    inference(superposition,[],[f11306,f1756])).

fof(f1756,plain,
    ( ! [X5] : sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))
    | ~ spl18_120 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f11306,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl18_517 ),
    inference(avatar_component_clause,[],[f11305])).

fof(f11310,plain,
    ( spl18_517
    | ~ spl18_302
    | ~ spl18_504 ),
    inference(avatar_split_clause,[],[f11303,f10943,f5522,f11305])).

fof(f5522,plain,
    ( spl18_302
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_302])])).

fof(f10943,plain,
    ( spl18_504
  <=> ! [X31,X30] : k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_504])])).

fof(f11303,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl18_302
    | ~ spl18_504 ),
    inference(superposition,[],[f5523,f10944])).

fof(f10944,plain,
    ( ! [X30,X31] : k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))
    | ~ spl18_504 ),
    inference(avatar_component_clause,[],[f10943])).

fof(f5523,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl18_302 ),
    inference(avatar_component_clause,[],[f5522])).

fof(f10945,plain,
    ( spl18_504
    | spl18_1
    | ~ spl18_4
    | ~ spl18_184 ),
    inference(avatar_split_clause,[],[f2909,f2753,f213,f198,f10943])).

fof(f213,plain,
    ( spl18_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f2753,plain,
    ( spl18_184
  <=> ! [X11,X12] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11))
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_184])])).

fof(f2909,plain,
    ( ! [X30,X31] : k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_184 ),
    inference(subsumption_resolution,[],[f2908,f200])).

fof(f2908,plain,
    ( ! [X30,X31] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_184 ),
    inference(subsumption_resolution,[],[f2894,f215])).

fof(f215,plain,
    ( l3_lattices(sK0)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f213])).

fof(f2894,plain,
    ( ! [X30,X31] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_184 ),
    inference(resolution,[],[f2754,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f2754,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(X12,u1_struct_0(sK0))
        | k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11)) )
    | ~ spl18_184 ),
    inference(avatar_component_clause,[],[f2753])).

fof(f10175,plain,
    ( spl18_463
    | ~ spl18_120
    | ~ spl18_282
    | ~ spl18_385 ),
    inference(avatar_split_clause,[],[f9992,f7639,f5220,f1755,f10173])).

fof(f5220,plain,
    ( spl18_282
  <=> ! [X0] : sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_282])])).

fof(f7639,plain,
    ( spl18_385
  <=> ! [X13] : sK12(sK0,X13) = k15_lattice3(sK0,X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_385])])).

fof(f9992,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))
    | ~ spl18_120
    | ~ spl18_282
    | ~ spl18_385 ),
    inference(forward_demodulation,[],[f5292,f7640])).

fof(f7640,plain,
    ( ! [X13] : sK12(sK0,X13) = k15_lattice3(sK0,X13)
    | ~ spl18_385 ),
    inference(avatar_component_clause,[],[f7639])).

fof(f5292,plain,
    ( ! [X1] : sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))
    | ~ spl18_120
    | ~ spl18_282 ),
    inference(superposition,[],[f5221,f1756])).

fof(f5221,plain,
    ( ! [X0] : sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl18_282 ),
    inference(avatar_component_clause,[],[f5220])).

fof(f7660,plain,
    ( spl18_386
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_369 ),
    inference(avatar_split_clause,[],[f7578,f7183,f427,f213,f208,f198,f7658])).

fof(f208,plain,
    ( spl18_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f427,plain,
    ( spl18_24
  <=> ! [X3] : m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).

fof(f7183,plain,
    ( spl18_369
  <=> ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_369])])).

fof(f7578,plain,
    ( ! [X3] : m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_369 ),
    inference(backward_demodulation,[],[f428,f7502])).

fof(f7502,plain,
    ( ! [X13] : sK12(sK0,X13) = k15_lattice3(sK0,X13)
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_369 ),
    inference(subsumption_resolution,[],[f7501,f200])).

fof(f7501,plain,
    ( ! [X13] :
        ( sK12(sK0,X13) = k15_lattice3(sK0,X13)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_369 ),
    inference(subsumption_resolution,[],[f7500,f215])).

fof(f7500,plain,
    ( ! [X13] :
        ( sK12(sK0,X13) = k15_lattice3(sK0,X13)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_369 ),
    inference(subsumption_resolution,[],[f7485,f210])).

fof(f210,plain,
    ( v4_lattice3(sK0)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f7485,plain,
    ( ! [X13] :
        ( sK12(sK0,X13) = k15_lattice3(sK0,X13)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_369 ),
    inference(resolution,[],[f7184,f156])).

fof(f156,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK12(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK11(X0,X2))
                & r4_lattice3(X0,sK11(X0,X2),sK10(X0))
                & m1_subset_1(sK11(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK10(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK12(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK12(X0,X4),X4)
              & m1_subset_1(sK12(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f87,f90,f89,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK10(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK10(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,sK10(X0))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK11(X0,X2))
        & r4_lattice3(X0,sK11(X0,X2),sK10(X0))
        & m1_subset_1(sK11(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK12(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK12(X0,X4),X4)
        & m1_subset_1(sK12(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

fof(f7184,plain,
    ( ! [X8] :
        ( ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | k15_lattice3(sK0,X8) = sK12(sK0,X8) )
    | ~ spl18_369 ),
    inference(avatar_component_clause,[],[f7183])).

fof(f428,plain,
    ( ! [X3] : m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))
    | ~ spl18_24 ),
    inference(avatar_component_clause,[],[f427])).

fof(f7641,plain,
    ( spl18_385
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_369 ),
    inference(avatar_split_clause,[],[f7502,f7183,f213,f208,f198,f7639])).

fof(f7185,plain,
    ( spl18_369
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(avatar_split_clause,[],[f5201,f4640,f427,f213,f208,f203,f198,f7183])).

fof(f203,plain,
    ( spl18_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f4640,plain,
    ( spl18_270
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1)
        | k15_lattice3(sK0,X0) = sK12(sK0,X1)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_270])])).

fof(f5201,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8) )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(subsumption_resolution,[],[f5200,f200])).

fof(f5200,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | v2_struct_0(sK0) )
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(subsumption_resolution,[],[f5199,f205])).

fof(f205,plain,
    ( v10_lattices(sK0)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f203])).

fof(f5199,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(subsumption_resolution,[],[f5198,f210])).

fof(f5198,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(subsumption_resolution,[],[f5197,f215])).

fof(f5197,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_24
    | ~ spl18_270 ),
    inference(subsumption_resolution,[],[f5196,f428])).

fof(f5196,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | ~ m1_subset_1(sK12(sK0,X8),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_270 ),
    inference(duplicate_literal_removal,[],[f5194])).

fof(f5194,plain,
    ( ! [X8] :
        ( k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | k15_lattice3(sK0,X8) = sK12(sK0,X8)
        | ~ r4_lattice3(sK0,sK12(sK0,X8),X8)
        | ~ m1_subset_1(sK12(sK0,X8),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_270 ),
    inference(resolution,[],[f4641,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,sK7(X0,X1,X2),X1)
      | k15_lattice3(X0,X1) = X2
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK7(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
                & r4_lattice3(X0,sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
        & r4_lattice3(X0,sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f4641,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1)
        | k15_lattice3(sK0,X0) = sK12(sK0,X1)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0) )
    | ~ spl18_270 ),
    inference(avatar_component_clause,[],[f4640])).

fof(f6437,plain,
    ( spl18_197
    | ~ spl18_13
    | ~ spl18_272 ),
    inference(avatar_split_clause,[],[f4811,f4660,f339,f3063])).

fof(f3063,plain,
    ( spl18_197
  <=> k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_197])])).

fof(f339,plain,
    ( spl18_13
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f4660,plain,
    ( spl18_272
  <=> ! [X0] :
        ( k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_272])])).

fof(f4811,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl18_13
    | ~ spl18_272 ),
    inference(resolution,[],[f4661,f341])).

fof(f341,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl18_13 ),
    inference(avatar_component_clause,[],[f339])).

fof(f4661,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 )
    | ~ spl18_272 ),
    inference(avatar_component_clause,[],[f4660])).

fof(f5524,plain,
    ( spl18_302
    | ~ spl18_187
    | ~ spl18_285 ),
    inference(avatar_split_clause,[],[f5336,f5237,f2768,f5522])).

fof(f2768,plain,
    ( spl18_187
  <=> ! [X11,X12] : k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_187])])).

fof(f5237,plain,
    ( spl18_285
  <=> ! [X22] : k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_285])])).

fof(f5336,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl18_187
    | ~ spl18_285 ),
    inference(superposition,[],[f2769,f5238])).

fof(f5238,plain,
    ( ! [X22] : k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))
    | ~ spl18_285 ),
    inference(avatar_component_clause,[],[f5237])).

fof(f2769,plain,
    ( ! [X12,X11] : k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))
    | ~ spl18_187 ),
    inference(avatar_component_clause,[],[f2768])).

fof(f5239,plain,
    ( spl18_285
    | spl18_1
    | ~ spl18_4
    | ~ spl18_272 ),
    inference(avatar_split_clause,[],[f4844,f4660,f213,f198,f5237])).

fof(f4844,plain,
    ( ! [X22] : k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_272 ),
    inference(subsumption_resolution,[],[f4843,f200])).

fof(f4843,plain,
    ( ! [X22] :
        ( k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_272 ),
    inference(subsumption_resolution,[],[f4833,f215])).

fof(f4833,plain,
    ( ! [X22] :
        ( k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_272 ),
    inference(resolution,[],[f4661,f170])).

fof(f5222,plain,
    ( spl18_282
    | ~ spl18_85
    | ~ spl18_189 ),
    inference(avatar_split_clause,[],[f4649,f2778,f1407,f5220])).

fof(f1407,plain,
    ( spl18_85
  <=> ! [X5] : k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_85])])).

fof(f2778,plain,
    ( spl18_189
  <=> ! [X11,X12] : sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_189])])).

fof(f4649,plain,
    ( ! [X0] : sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl18_85
    | ~ spl18_189 ),
    inference(superposition,[],[f2779,f1408])).

fof(f1408,plain,
    ( ! [X5] : k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))
    | ~ spl18_85 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f2779,plain,
    ( ! [X12,X11] : sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))
    | ~ spl18_189 ),
    inference(avatar_component_clause,[],[f2778])).

fof(f4662,plain,
    ( spl18_272
    | ~ spl18_28
    | ~ spl18_175 ),
    inference(avatar_split_clause,[],[f2695,f2473,f484,f4660])).

fof(f484,plain,
    ( spl18_28
  <=> ! [X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r4_lattice3(sK0,X16,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_28])])).

fof(f2473,plain,
    ( spl18_175
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_175])])).

fof(f2695,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_28
    | ~ spl18_175 ),
    inference(duplicate_literal_removal,[],[f2678])).

fof(f2678,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_28
    | ~ spl18_175 ),
    inference(resolution,[],[f2474,f485])).

fof(f485,plain,
    ( ! [X16] :
        ( r4_lattice3(sK0,X16,k1_xboole_0)
        | ~ m1_subset_1(X16,u1_struct_0(sK0)) )
    | ~ spl18_28 ),
    inference(avatar_component_clause,[],[f484])).

fof(f2474,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_175 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f4642,plain,
    ( spl18_270
    | ~ spl18_24
    | ~ spl18_38
    | ~ spl18_132 ),
    inference(avatar_split_clause,[],[f2003,f1994,f650,f427,f4640])).

fof(f650,plain,
    ( spl18_38
  <=> ! [X1,X0] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_38])])).

fof(f1994,plain,
    ( spl18_132
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_132])])).

fof(f2003,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1)
        | k15_lattice3(sK0,X0) = sK12(sK0,X1)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0) )
    | ~ spl18_24
    | ~ spl18_38
    | ~ spl18_132 ),
    inference(subsumption_resolution,[],[f2002,f428])).

fof(f2002,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1)
        | k15_lattice3(sK0,X0) = sK12(sK0,X1)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0)
        | ~ m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl18_38
    | ~ spl18_132 ),
    inference(duplicate_literal_removal,[],[f2001])).

fof(f2001,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1)
        | k15_lattice3(sK0,X0) = sK12(sK0,X1)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0)
        | ~ r4_lattice3(sK0,sK12(sK0,X1),X0)
        | ~ m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = sK12(sK0,X1) )
    | ~ spl18_38
    | ~ spl18_132 ),
    inference(resolution,[],[f1995,f651])).

fof(f651,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = X1 )
    | ~ spl18_38 ),
    inference(avatar_component_clause,[],[f650])).

fof(f1995,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2) )
    | ~ spl18_132 ),
    inference(avatar_component_clause,[],[f1994])).

fof(f3273,plain,
    ( spl18_6
    | ~ spl18_168
    | ~ spl18_172
    | ~ spl18_197 ),
    inference(avatar_split_clause,[],[f3254,f3063,f2459,f2436,f229])).

fof(f229,plain,
    ( spl18_6
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f2436,plain,
    ( spl18_168
  <=> ! [X11] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_168])])).

fof(f2459,plain,
    ( spl18_172
  <=> ! [X10] : k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_172])])).

fof(f3254,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ spl18_168
    | ~ spl18_172
    | ~ spl18_197 ),
    inference(forward_demodulation,[],[f3251,f2437])).

fof(f2437,plain,
    ( ! [X11] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))
    | ~ spl18_168 ),
    inference(avatar_component_clause,[],[f2436])).

fof(f3251,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl18_172
    | ~ spl18_197 ),
    inference(superposition,[],[f2460,f3065])).

fof(f3065,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl18_197 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f2460,plain,
    ( ! [X10] : k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))
    | ~ spl18_172 ),
    inference(avatar_component_clause,[],[f2459])).

fof(f2780,plain,
    ( spl18_189
    | spl18_1
    | ~ spl18_4
    | ~ spl18_74 ),
    inference(avatar_split_clause,[],[f1361,f1285,f213,f198,f2778])).

fof(f1285,plain,
    ( spl18_74
  <=> ! [X16,X17] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_74])])).

fof(f1361,plain,
    ( ! [X12,X11] : sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_74 ),
    inference(subsumption_resolution,[],[f1360,f200])).

fof(f1360,plain,
    ( ! [X12,X11] :
        ( sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_74 ),
    inference(subsumption_resolution,[],[f1348,f215])).

fof(f1348,plain,
    ( ! [X12,X11] :
        ( sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_74 ),
    inference(resolution,[],[f1286,f170])).

fof(f1286,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) )
    | ~ spl18_74 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f2770,plain,
    ( spl18_187
    | spl18_1
    | ~ spl18_4
    | ~ spl18_73 ),
    inference(avatar_split_clause,[],[f1327,f1275,f213,f198,f2768])).

fof(f1275,plain,
    ( spl18_73
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_73])])).

fof(f1327,plain,
    ( ! [X12,X11] : k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f1326,f200])).

fof(f1326,plain,
    ( ! [X12,X11] :
        ( k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f1314,f215])).

fof(f1314,plain,
    ( ! [X12,X11] :
        ( k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_73 ),
    inference(resolution,[],[f1276,f170])).

fof(f1276,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)) )
    | ~ spl18_73 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f2755,plain,
    ( spl18_184
    | spl18_1
    | ~ spl18_4
    | ~ spl18_50 ),
    inference(avatar_split_clause,[],[f1158,f848,f213,f198,f2753])).

fof(f848,plain,
    ( spl18_50
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_50])])).

fof(f1158,plain,
    ( ! [X12,X11] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11))
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) )
    | spl18_1
    | ~ spl18_4
    | ~ spl18_50 ),
    inference(subsumption_resolution,[],[f1157,f200])).

fof(f1157,plain,
    ( ! [X12,X11] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_50 ),
    inference(subsumption_resolution,[],[f1145,f215])).

fof(f1145,plain,
    ( ! [X12,X11] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_50 ),
    inference(resolution,[],[f849,f170])).

fof(f849,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_50 ),
    inference(avatar_component_clause,[],[f848])).

fof(f2475,plain,
    ( spl18_175
    | spl18_1
    | ~ spl18_4
    | ~ spl18_88 ),
    inference(avatar_split_clause,[],[f1465,f1451,f213,f198,f2473])).

fof(f1451,plain,
    ( spl18_88
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_88])])).

fof(f1465,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl18_1
    | ~ spl18_4
    | ~ spl18_88 ),
    inference(subsumption_resolution,[],[f1464,f200])).

fof(f1464,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_88 ),
    inference(subsumption_resolution,[],[f1459,f215])).

fof(f1459,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_88 ),
    inference(resolution,[],[f1452,f170])).

fof(f1452,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_88 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f2461,plain,
    ( spl18_172
    | spl18_1
    | ~ spl18_11
    | ~ spl18_73 ),
    inference(avatar_split_clause,[],[f1325,f1275,f320,f198,f2459])).

fof(f1325,plain,
    ( ! [X10] : k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))
    | spl18_1
    | ~ spl18_11
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f1324,f200])).

fof(f1324,plain,
    ( ! [X10] :
        ( k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl18_11
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f1313,f321])).

fof(f1313,plain,
    ( ! [X10] :
        ( k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_73 ),
    inference(resolution,[],[f1276,f127])).

fof(f127,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f2438,plain,
    ( spl18_168
    | spl18_1
    | ~ spl18_4
    | ~ spl18_56
    | ~ spl18_124 ),
    inference(avatar_split_clause,[],[f2415,f1771,f1014,f213,f198,f2436])).

fof(f1014,plain,
    ( spl18_56
  <=> ! [X5] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_56])])).

fof(f1771,plain,
    ( spl18_124
  <=> ! [X10] :
        ( k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_124])])).

fof(f2415,plain,
    ( ! [X11] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_56
    | ~ spl18_124 ),
    inference(forward_demodulation,[],[f2414,f1015])).

fof(f1015,plain,
    ( ! [X5] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))
    | ~ spl18_56 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f2414,plain,
    ( ! [X11] : k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_124 ),
    inference(subsumption_resolution,[],[f2413,f200])).

fof(f2413,plain,
    ( ! [X11] :
        ( k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_124 ),
    inference(subsumption_resolution,[],[f2396,f215])).

fof(f2396,plain,
    ( ! [X11] :
        ( k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_124 ),
    inference(resolution,[],[f1772,f170])).

fof(f1772,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,u1_struct_0(sK0))
        | k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0)) )
    | ~ spl18_124 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f1996,plain,
    ( spl18_132
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(avatar_split_clause,[],[f510,f480,f427,f213,f208,f203,f198,f1994])).

fof(f480,plain,
    ( spl18_27
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK12(sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_27])])).

fof(f510,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2) )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f509,f200])).

fof(f509,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2)
        | v2_struct_0(sK0) )
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f508,f205])).

fof(f508,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f507,f210])).

fof(f507,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f506,f215])).

fof(f506,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f500,f428])).

fof(f500,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3)
        | k15_lattice3(sK0,X2) = sK12(sK0,X3)
        | ~ r4_lattice3(sK0,sK12(sK0,X3),X2)
        | ~ m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_27 ),
    inference(resolution,[],[f481,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f481,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,sK12(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl18_27 ),
    inference(avatar_component_clause,[],[f480])).

fof(f1773,plain,
    ( spl18_124
    | spl18_1
    | ~ spl18_11
    | ~ spl18_50 ),
    inference(avatar_split_clause,[],[f1156,f848,f320,f198,f1771])).

fof(f1156,plain,
    ( ! [X10] :
        ( k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0)) )
    | spl18_1
    | ~ spl18_11
    | ~ spl18_50 ),
    inference(subsumption_resolution,[],[f1155,f200])).

fof(f1155,plain,
    ( ! [X10] :
        ( k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_11
    | ~ spl18_50 ),
    inference(subsumption_resolution,[],[f1144,f321])).

fof(f1144,plain,
    ( ! [X10] :
        ( k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_50 ),
    inference(resolution,[],[f849,f127])).

fof(f1757,plain,
    ( spl18_120
    | spl18_1
    | ~ spl18_4
    | ~ spl18_47 ),
    inference(avatar_split_clause,[],[f1042,f764,f213,f198,f1755])).

fof(f764,plain,
    ( spl18_47
  <=> ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_47])])).

fof(f1042,plain,
    ( ! [X5] : sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_47 ),
    inference(subsumption_resolution,[],[f1041,f200])).

fof(f1041,plain,
    ( ! [X5] :
        ( sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_47 ),
    inference(subsumption_resolution,[],[f1029,f215])).

fof(f1029,plain,
    ( ! [X5] :
        ( sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_47 ),
    inference(resolution,[],[f765,f170])).

fof(f765,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) )
    | ~ spl18_47 ),
    inference(avatar_component_clause,[],[f764])).

fof(f1453,plain,
    ( spl18_88
    | spl18_1
    | ~ spl18_30
    | ~ spl18_66 ),
    inference(avatar_split_clause,[],[f1440,f1178,f492,f198,f1451])).

fof(f492,plain,
    ( spl18_30
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_30])])).

fof(f1178,plain,
    ( spl18_66
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_66])])).

fof(f1440,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl18_1
    | ~ spl18_30
    | ~ spl18_66 ),
    inference(subsumption_resolution,[],[f553,f1179])).

fof(f1179,plain,
    ( l2_lattices(sK0)
    | ~ spl18_66 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f553,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0) )
    | spl18_1
    | ~ spl18_30 ),
    inference(subsumption_resolution,[],[f552,f200])).

fof(f552,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_30 ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_30 ),
    inference(resolution,[],[f493,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f493,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl18_30 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1409,plain,
    ( spl18_85
    | spl18_1
    | ~ spl18_4
    | ~ spl18_70 ),
    inference(avatar_split_clause,[],[f1249,f1223,f213,f198,f1407])).

fof(f1223,plain,
    ( spl18_70
  <=> ! [X0] :
        ( k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).

fof(f1249,plain,
    ( ! [X5] : k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f1248,f200])).

fof(f1248,plain,
    ( ! [X5] :
        ( k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f1236,f215])).

fof(f1236,plain,
    ( ! [X5] :
        ( k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_70 ),
    inference(resolution,[],[f1224,f170])).

fof(f1224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0 )
    | ~ spl18_70 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f1287,plain,
    ( spl18_74
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(avatar_split_clause,[],[f631,f589,f213,f208,f198,f1285])).

fof(f589,plain,
    ( spl18_37
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_37])])).

fof(f631,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) )
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f630,f200])).

fof(f630,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16))
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f629,f215])).

fof(f629,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f611,f210])).

fof(f611,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_37 ),
    inference(resolution,[],[f590,f155])).

fof(f155,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK12(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f590,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 )
    | ~ spl18_37 ),
    inference(avatar_component_clause,[],[f589])).

fof(f1277,plain,
    ( spl18_73
    | spl18_1
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(avatar_split_clause,[],[f617,f589,f213,f198,f1275])).

fof(f617,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)) )
    | spl18_1
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f616,f200])).

fof(f616,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f604,f215])).

fof(f604,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_37 ),
    inference(resolution,[],[f590,f170])).

fof(f1225,plain,
    ( spl18_70
    | ~ spl18_28
    | ~ spl18_67 ),
    inference(avatar_split_clause,[],[f1202,f1182,f484,f1223])).

fof(f1182,plain,
    ( spl18_67
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_67])])).

fof(f1202,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_28
    | ~ spl18_67 ),
    inference(duplicate_literal_removal,[],[f1194])).

fof(f1194,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_28
    | ~ spl18_67 ),
    inference(resolution,[],[f1183,f485])).

fof(f1183,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_67 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1189,plain,
    ( ~ spl18_4
    | spl18_66 ),
    inference(avatar_contradiction_clause,[],[f1188])).

fof(f1188,plain,
    ( $false
    | ~ spl18_4
    | spl18_66 ),
    inference(subsumption_resolution,[],[f1186,f215])).

fof(f1186,plain,
    ( ~ l3_lattices(sK0)
    | spl18_66 ),
    inference(resolution,[],[f1180,f117])).

fof(f117,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f1180,plain,
    ( ~ l2_lattices(sK0)
    | spl18_66 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f1184,plain,
    ( ~ spl18_66
    | spl18_67
    | spl18_1
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(avatar_split_clause,[],[f505,f480,f427,f198,f1182,f1178])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ l2_lattices(sK0) )
    | spl18_1
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f504,f200])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_24
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f503,f428])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_27 ),
    inference(duplicate_literal_removal,[],[f499])).

fof(f499,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,sK12(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_27 ),
    inference(resolution,[],[f481,f125])).

fof(f1016,plain,
    ( spl18_56
    | spl18_1
    | ~ spl18_4
    | ~ spl18_48 ),
    inference(avatar_split_clause,[],[f993,f807,f213,f198,f1014])).

fof(f807,plain,
    ( spl18_48
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_48])])).

fof(f993,plain,
    ( ! [X5] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_48 ),
    inference(subsumption_resolution,[],[f992,f200])).

fof(f992,plain,
    ( ! [X5] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_48 ),
    inference(subsumption_resolution,[],[f982,f215])).

fof(f982,plain,
    ( ! [X5] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_48 ),
    inference(resolution,[],[f808,f170])).

fof(f808,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl18_48 ),
    inference(avatar_component_clause,[],[f807])).

fof(f850,plain,
    ( spl18_50
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f663,f213,f203,f198,f848])).

fof(f663,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f662,f215])).

fof(f662,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0) )
    | spl18_1
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f661,f200])).

fof(f661,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0) )
    | ~ spl18_2 ),
    inference(resolution,[],[f392,f205])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f391,f116])).

fof(f116,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f137,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f137,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f809,plain,
    ( spl18_48
    | spl18_1
    | ~ spl18_5
    | ~ spl18_11 ),
    inference(avatar_split_clause,[],[f796,f320,f225,f198,f807])).

fof(f796,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) )
    | spl18_1
    | ~ spl18_5
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f795,f200])).

fof(f795,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)
        | v2_struct_0(sK0) )
    | ~ spl18_5
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f788,f321])).

fof(f788,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_5 ),
    inference(resolution,[],[f226,f419])).

fof(f419,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f185,f127])).

fof(f185,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f226,plain,
    ( v13_lattices(sK0)
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f225])).

fof(f766,plain,
    ( spl18_47
    | spl18_1
    | spl18_5
    | ~ spl18_9
    | ~ spl18_11 ),
    inference(avatar_split_clause,[],[f761,f320,f250,f225,f198,f764])).

fof(f250,plain,
    ( spl18_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f761,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl18_1
    | spl18_5
    | ~ spl18_9
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f271,f321])).

fof(f271,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0) )
    | spl18_1
    | spl18_5
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f270,f200])).

fof(f270,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl18_5
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f259,f227])).

fof(f259,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_9 ),
    inference(resolution,[],[f251,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 )
    | ~ spl18_9 ),
    inference(avatar_component_clause,[],[f250])).

fof(f652,plain,
    ( spl18_38
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f444,f213,f208,f203,f198,f650])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = X1 )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f443,f200])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = X1
        | v2_struct_0(sK0) )
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f442,f205])).

fof(f442,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = X1
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f441,f215])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = X1
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3 ),
    inference(resolution,[],[f194,f210])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = X2
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f599,plain,
    ( spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | spl18_16 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | spl18_16 ),
    inference(subsumption_resolution,[],[f597,f215])).

fof(f597,plain,
    ( ~ l3_lattices(sK0)
    | spl18_1
    | ~ spl18_2
    | spl18_16 ),
    inference(subsumption_resolution,[],[f596,f200])).

fof(f596,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl18_2
    | spl18_16 ),
    inference(subsumption_resolution,[],[f594,f205])).

fof(f594,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl18_16 ),
    inference(resolution,[],[f360,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f360,plain,
    ( ~ v9_lattices(sK0)
    | spl18_16 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl18_16
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).

fof(f591,plain,
    ( spl18_37
    | spl18_1
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f403,f359,f213,f198,f589])).

fof(f403,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 )
    | spl18_1
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f402,f200])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f401,f361])).

fof(f361,plain,
    ( v9_lattices(sK0)
    | ~ spl18_16 ),
    inference(avatar_component_clause,[],[f359])).

fof(f401,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v9_lattices(sK0)
        | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1
        | v2_struct_0(sK0) )
    | ~ spl18_4 ),
    inference(resolution,[],[f151,f215])).

fof(f151,plain,(
    ! [X4,X0,X3] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f82,f84,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f494,plain,
    ( spl18_30
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f440,f213,f208,f203,f198,f492])).

fof(f440,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f439,f200])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f438,f205])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f437,f215])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3 ),
    inference(resolution,[],[f436,f210])).

fof(f436,plain,(
    ! [X4,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f193,f170])).

fof(f193,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f486,plain,
    ( spl18_28
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f468,f242,f484])).

fof(f242,plain,
    ( spl18_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK14(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f468,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r4_lattice3(sK0,X16,k1_xboole_0) )
    | ~ spl18_8 ),
    inference(resolution,[],[f243,f217])).

fof(f217,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f169,f188])).

fof(f188,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f169,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f243,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK14(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f482,plain,
    ( spl18_27
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f347,f213,f208,f198,f480])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK12(sK0,X1),X0) )
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f346,f200])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK12(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f345,f215])).

fof(f345,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK12(sK0,X1),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3 ),
    inference(resolution,[],[f157,f210])).

fof(f157,plain,(
    ! [X6,X4,X0] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r1_lattices(X0,sK12(X0,X4),X6)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f429,plain,
    ( spl18_24
    | spl18_1
    | ~ spl18_4
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f425,f387,f213,f198,f427])).

fof(f387,plain,
    ( spl18_20
  <=> ! [X2] : sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f425,plain,
    ( ! [X3] : m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f424,f200])).

fof(f424,plain,
    ( ! [X3] :
        ( m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f423,f215])).

fof(f423,plain,
    ( ! [X3] :
        ( m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_20 ),
    inference(superposition,[],[f170,f388])).

fof(f388,plain,
    ( ! [X2] : sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))
    | ~ spl18_20 ),
    inference(avatar_component_clause,[],[f387])).

fof(f389,plain,
    ( spl18_20
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_9 ),
    inference(avatar_split_clause,[],[f280,f250,f213,f208,f198,f387])).

fof(f280,plain,
    ( ! [X2] : sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))
    | spl18_1
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f279,f200])).

fof(f279,plain,
    ( ! [X2] :
        ( sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f278,f215])).

fof(f278,plain,
    ( ! [X2] :
        ( sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f265,f210])).

fof(f265,plain,
    ( ! [X2] :
        ( sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_9 ),
    inference(resolution,[],[f251,f155])).

fof(f342,plain,
    ( spl18_13
    | spl18_1
    | ~ spl18_4
    | ~ spl18_12 ),
    inference(avatar_split_clause,[],[f337,f324,f213,f198,f339])).

fof(f324,plain,
    ( spl18_12
  <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f337,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_4
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f336,f200])).

fof(f336,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl18_4
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f335,f215])).

fof(f335,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_12 ),
    inference(superposition,[],[f170,f326])).

fof(f326,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f324])).

fof(f334,plain,
    ( ~ spl18_4
    | spl18_11 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl18_4
    | spl18_11 ),
    inference(subsumption_resolution,[],[f331,f215])).

fof(f331,plain,
    ( ~ l3_lattices(sK0)
    | spl18_11 ),
    inference(resolution,[],[f322,f116])).

fof(f322,plain,
    ( ~ l1_lattices(sK0)
    | spl18_11 ),
    inference(avatar_component_clause,[],[f320])).

fof(f327,plain,
    ( ~ spl18_11
    | spl18_12
    | spl18_1
    | ~ spl18_9 ),
    inference(avatar_split_clause,[],[f267,f250,f198,f324,f320])).

fof(f267,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | spl18_1
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f257,f200])).

fof(f257,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_9 ),
    inference(resolution,[],[f251,f127])).

fof(f252,plain,
    ( spl18_9
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f248,f213,f208,f203,f198,f250])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 )
    | spl18_1
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f247,f200])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl18_2
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f246,f205])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f245,f215])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_3 ),
    inference(resolution,[],[f141,f210])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f244,plain,
    ( spl18_8
    | spl18_1
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f236,f213,f198,f242])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK14(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl18_1
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f235,f200])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK14(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl18_4 ),
    inference(resolution,[],[f167,f215])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK14(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK14(X0,X1,X2),X1)
                  & r2_hidden(sK14(X0,X1,X2),X2)
                  & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f97,f98])).

fof(f98,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK14(X0,X1,X2),X1)
        & r2_hidden(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f232,plain,
    ( ~ spl18_5
    | ~ spl18_6
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f223,f213,f203,f198,f229,f225])).

fof(f223,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f222,f200])).

fof(f222,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f221,f205])).

fof(f221,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f115,f215])).

fof(f115,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f216,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f114,f213])).

fof(f114,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f211,plain,(
    spl18_3 ),
    inference(avatar_split_clause,[],[f113,f208])).

fof(f113,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f206,plain,(
    spl18_2 ),
    inference(avatar_split_clause,[],[f112,f203])).

fof(f112,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f201,plain,(
    ~ spl18_1 ),
    inference(avatar_split_clause,[],[f111,f198])).

fof(f111,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:28:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (25291)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (25301)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (25285)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (25286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (25287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (25288)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (25284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25300)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (25302)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (25299)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (25294)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (25294)Refutation not found, incomplete strategy% (25294)------------------------------
% 0.22/0.52  % (25294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25294)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25294)Memory used [KB]: 10618
% 0.22/0.52  % (25294)Time elapsed: 0.002 s
% 0.22/0.52  % (25294)------------------------------
% 0.22/0.52  % (25294)------------------------------
% 0.22/0.52  % (25297)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (25303)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25290)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (25295)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (25292)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (25305)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (25289)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (25304)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (25289)Refutation not found, incomplete strategy% (25289)------------------------------
% 0.22/0.53  % (25289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25289)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25289)Memory used [KB]: 10618
% 0.22/0.53  % (25289)Time elapsed: 0.002 s
% 0.22/0.53  % (25289)------------------------------
% 0.22/0.53  % (25289)------------------------------
% 0.22/0.53  % (25307)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (25293)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (25283)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (25296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (25283)Refutation not found, incomplete strategy% (25283)------------------------------
% 0.22/0.53  % (25283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25283)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25283)Memory used [KB]: 10618
% 0.22/0.53  % (25283)Time elapsed: 0.117 s
% 0.22/0.53  % (25283)------------------------------
% 0.22/0.53  % (25283)------------------------------
% 0.22/0.53  % (25296)Refutation not found, incomplete strategy% (25296)------------------------------
% 0.22/0.53  % (25296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25296)Memory used [KB]: 6140
% 0.22/0.53  % (25296)Time elapsed: 0.118 s
% 0.22/0.53  % (25296)------------------------------
% 0.22/0.53  % (25296)------------------------------
% 0.22/0.54  % (25284)Refutation not found, incomplete strategy% (25284)------------------------------
% 0.22/0.54  % (25284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25284)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25284)Memory used [KB]: 10746
% 0.22/0.54  % (25284)Time elapsed: 0.114 s
% 0.22/0.54  % (25284)------------------------------
% 0.22/0.54  % (25284)------------------------------
% 1.43/0.54  % (25298)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.43/0.54  % (25308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.43/0.55  % (25306)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 2.20/0.65  % (25292)Refutation not found, incomplete strategy% (25292)------------------------------
% 2.20/0.65  % (25292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (25292)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (25292)Memory used [KB]: 6140
% 2.20/0.66  % (25292)Time elapsed: 0.194 s
% 2.20/0.66  % (25292)------------------------------
% 2.20/0.66  % (25292)------------------------------
% 2.20/0.66  % (25300)Refutation not found, incomplete strategy% (25300)------------------------------
% 2.20/0.66  % (25300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (25300)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (25300)Memory used [KB]: 6524
% 2.20/0.66  % (25300)Time elapsed: 0.208 s
% 2.20/0.66  % (25300)------------------------------
% 2.20/0.66  % (25300)------------------------------
% 4.54/0.96  % (25297)Time limit reached!
% 4.54/0.96  % (25297)------------------------------
% 4.54/0.96  % (25297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.96  % (25297)Termination reason: Time limit
% 4.54/0.96  
% 4.54/0.96  % (25297)Memory used [KB]: 9210
% 4.54/0.96  % (25297)Time elapsed: 0.512 s
% 4.54/0.96  % (25297)------------------------------
% 4.54/0.96  % (25297)------------------------------
% 6.95/1.24  % (25285)Refutation found. Thanks to Tanya!
% 6.95/1.24  % SZS status Theorem for theBenchmark
% 6.95/1.24  % SZS output start Proof for theBenchmark
% 6.95/1.24  fof(f11358,plain,(
% 6.95/1.24    $false),
% 6.95/1.24    inference(avatar_sat_refutation,[],[f201,f206,f211,f216,f232,f244,f252,f327,f334,f342,f389,f429,f482,f486,f494,f591,f599,f652,f766,f809,f850,f1016,f1184,f1189,f1225,f1277,f1287,f1409,f1453,f1757,f1773,f1996,f2438,f2461,f2475,f2755,f2770,f2780,f3273,f4642,f4662,f5222,f5239,f5524,f6437,f7185,f7641,f7660,f10175,f10945,f11310,f11333,f11357])).
% 6.95/1.24  fof(f11357,plain,(
% 6.95/1.24    spl18_1 | spl18_5 | ~spl18_11 | ~spl18_386 | ~spl18_463 | ~spl18_520),
% 6.95/1.24    inference(avatar_contradiction_clause,[],[f11356])).
% 6.95/1.24  fof(f11356,plain,(
% 6.95/1.24    $false | (spl18_1 | spl18_5 | ~spl18_11 | ~spl18_386 | ~spl18_463 | ~spl18_520)),
% 6.95/1.24    inference(subsumption_resolution,[],[f11355,f200])).
% 6.95/1.24  fof(f200,plain,(
% 6.95/1.24    ~v2_struct_0(sK0) | spl18_1),
% 6.95/1.24    inference(avatar_component_clause,[],[f198])).
% 6.95/1.24  fof(f198,plain,(
% 6.95/1.24    spl18_1 <=> v2_struct_0(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).
% 6.95/1.24  fof(f11355,plain,(
% 6.95/1.24    v2_struct_0(sK0) | (spl18_5 | ~spl18_11 | ~spl18_386 | ~spl18_463 | ~spl18_520)),
% 6.95/1.24    inference(subsumption_resolution,[],[f11354,f321])).
% 6.95/1.24  fof(f321,plain,(
% 6.95/1.24    l1_lattices(sK0) | ~spl18_11),
% 6.95/1.24    inference(avatar_component_clause,[],[f320])).
% 6.95/1.24  fof(f320,plain,(
% 6.95/1.24    spl18_11 <=> l1_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).
% 6.95/1.24  fof(f11354,plain,(
% 6.95/1.24    ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl18_5 | ~spl18_386 | ~spl18_463 | ~spl18_520)),
% 6.95/1.24    inference(subsumption_resolution,[],[f11353,f7659])).
% 6.95/1.24  fof(f7659,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))) ) | ~spl18_386),
% 6.95/1.24    inference(avatar_component_clause,[],[f7658])).
% 6.95/1.24  fof(f7658,plain,(
% 6.95/1.24    spl18_386 <=> ! [X3] : m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_386])])).
% 6.95/1.24  fof(f11353,plain,(
% 6.95/1.24    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl18_5 | ~spl18_463 | ~spl18_520)),
% 6.95/1.24    inference(subsumption_resolution,[],[f11352,f10174])).
% 6.95/1.24  fof(f10174,plain,(
% 6.95/1.24    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | ~spl18_463),
% 6.95/1.24    inference(avatar_component_clause,[],[f10173])).
% 6.95/1.24  fof(f10173,plain,(
% 6.95/1.24    spl18_463 <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_463])])).
% 6.95/1.24  fof(f11352,plain,(
% 6.95/1.24    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl18_5 | ~spl18_520)),
% 6.95/1.24    inference(subsumption_resolution,[],[f11350,f227])).
% 6.95/1.24  fof(f227,plain,(
% 6.95/1.24    ~v13_lattices(sK0) | spl18_5),
% 6.95/1.24    inference(avatar_component_clause,[],[f225])).
% 6.95/1.24  fof(f225,plain,(
% 6.95/1.24    spl18_5 <=> v13_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 6.95/1.24  fof(f11350,plain,(
% 6.95/1.24    v13_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl18_520),
% 6.95/1.24    inference(trivial_inequality_removal,[],[f11349])).
% 6.95/1.24  fof(f11349,plain,(
% 6.95/1.24    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | v13_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl18_520),
% 6.95/1.24    inference(superposition,[],[f136,f11332])).
% 6.95/1.24  fof(f11332,plain,(
% 6.95/1.24    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))) ) | ~spl18_520),
% 6.95/1.24    inference(avatar_component_clause,[],[f11331])).
% 6.95/1.24  fof(f11331,plain,(
% 6.95/1.24    spl18_520 <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_520])])).
% 6.95/1.24  fof(f136,plain,(
% 6.95/1.24    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f68])).
% 6.95/1.24  fof(f68,plain,(
% 6.95/1.24    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f65,f67,f66])).
% 6.95/1.24  fof(f66,plain,(
% 6.95/1.24    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f67,plain,(
% 6.95/1.24    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f65,plain,(
% 6.95/1.24    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f64])).
% 6.95/1.24  fof(f64,plain,(
% 6.95/1.24    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f34])).
% 6.95/1.24  fof(f34,plain,(
% 6.95/1.24    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f33])).
% 6.95/1.24  fof(f33,plain,(
% 6.95/1.24    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f9])).
% 6.95/1.24  fof(f9,axiom,(
% 6.95/1.24    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 6.95/1.24  fof(f11333,plain,(
% 6.95/1.24    spl18_520 | ~spl18_120 | ~spl18_517),
% 6.95/1.24    inference(avatar_split_clause,[],[f11314,f11305,f1755,f11331])).
% 6.95/1.24  fof(f1755,plain,(
% 6.95/1.24    spl18_120 <=> ! [X5] : sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_120])])).
% 6.95/1.24  fof(f11305,plain,(
% 6.95/1.24    spl18_517 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_517])])).
% 6.95/1.24  fof(f11314,plain,(
% 6.95/1.24    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))) ) | (~spl18_120 | ~spl18_517)),
% 6.95/1.24    inference(superposition,[],[f11306,f1756])).
% 6.95/1.24  fof(f1756,plain,(
% 6.95/1.24    ( ! [X5] : (sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))) ) | ~spl18_120),
% 6.95/1.24    inference(avatar_component_clause,[],[f1755])).
% 6.95/1.24  fof(f11306,plain,(
% 6.95/1.24    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))) ) | ~spl18_517),
% 6.95/1.24    inference(avatar_component_clause,[],[f11305])).
% 6.95/1.24  fof(f11310,plain,(
% 6.95/1.24    spl18_517 | ~spl18_302 | ~spl18_504),
% 6.95/1.24    inference(avatar_split_clause,[],[f11303,f10943,f5522,f11305])).
% 6.95/1.24  fof(f5522,plain,(
% 6.95/1.24    spl18_302 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_302])])).
% 6.95/1.24  fof(f10943,plain,(
% 6.95/1.24    spl18_504 <=> ! [X31,X30] : k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_504])])).
% 6.95/1.24  fof(f11303,plain,(
% 6.95/1.24    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))) ) | (~spl18_302 | ~spl18_504)),
% 6.95/1.24    inference(superposition,[],[f5523,f10944])).
% 6.95/1.24  fof(f10944,plain,(
% 6.95/1.24    ( ! [X30,X31] : (k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))) ) | ~spl18_504),
% 6.95/1.24    inference(avatar_component_clause,[],[f10943])).
% 6.95/1.24  fof(f5523,plain,(
% 6.95/1.24    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl18_302),
% 6.95/1.24    inference(avatar_component_clause,[],[f5522])).
% 6.95/1.24  fof(f10945,plain,(
% 6.95/1.24    spl18_504 | spl18_1 | ~spl18_4 | ~spl18_184),
% 6.95/1.24    inference(avatar_split_clause,[],[f2909,f2753,f213,f198,f10943])).
% 6.95/1.24  fof(f213,plain,(
% 6.95/1.24    spl18_4 <=> l3_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 6.95/1.24  fof(f2753,plain,(
% 6.95/1.24    spl18_184 <=> ! [X11,X12] : (k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11)) | ~m1_subset_1(X12,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_184])])).
% 6.95/1.24  fof(f2909,plain,(
% 6.95/1.24    ( ! [X30,X31] : (k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30))) ) | (spl18_1 | ~spl18_4 | ~spl18_184)),
% 6.95/1.24    inference(subsumption_resolution,[],[f2908,f200])).
% 6.95/1.24  fof(f2908,plain,(
% 6.95/1.24    ( ! [X30,X31] : (k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_184)),
% 6.95/1.24    inference(subsumption_resolution,[],[f2894,f215])).
% 6.95/1.24  fof(f215,plain,(
% 6.95/1.24    l3_lattices(sK0) | ~spl18_4),
% 6.95/1.24    inference(avatar_component_clause,[],[f213])).
% 6.95/1.24  fof(f2894,plain,(
% 6.95/1.24    ( ! [X30,X31] : (k2_lattices(sK0,k15_lattice3(sK0,X30),k15_lattice3(sK0,X31)) = k2_lattices(sK0,k15_lattice3(sK0,X31),k15_lattice3(sK0,X30)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_184),
% 6.95/1.24    inference(resolution,[],[f2754,f170])).
% 6.95/1.24  fof(f170,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f52])).
% 6.95/1.24  fof(f52,plain,(
% 6.95/1.24    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f51])).
% 6.95/1.24  fof(f51,plain,(
% 6.95/1.24    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f15])).
% 6.95/1.24  fof(f15,axiom,(
% 6.95/1.24    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 6.95/1.24  fof(f2754,plain,(
% 6.95/1.24    ( ! [X12,X11] : (~m1_subset_1(X12,u1_struct_0(sK0)) | k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11))) ) | ~spl18_184),
% 6.95/1.24    inference(avatar_component_clause,[],[f2753])).
% 6.95/1.24  fof(f10175,plain,(
% 6.95/1.24    spl18_463 | ~spl18_120 | ~spl18_282 | ~spl18_385),
% 6.95/1.24    inference(avatar_split_clause,[],[f9992,f7639,f5220,f1755,f10173])).
% 6.95/1.24  fof(f5220,plain,(
% 6.95/1.24    spl18_282 <=> ! [X0] : sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_282])])).
% 6.95/1.24  fof(f7639,plain,(
% 6.95/1.24    spl18_385 <=> ! [X13] : sK12(sK0,X13) = k15_lattice3(sK0,X13)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_385])])).
% 6.95/1.24  fof(f9992,plain,(
% 6.95/1.24    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | (~spl18_120 | ~spl18_282 | ~spl18_385)),
% 6.95/1.24    inference(forward_demodulation,[],[f5292,f7640])).
% 6.95/1.24  fof(f7640,plain,(
% 6.95/1.24    ( ! [X13] : (sK12(sK0,X13) = k15_lattice3(sK0,X13)) ) | ~spl18_385),
% 6.95/1.24    inference(avatar_component_clause,[],[f7639])).
% 6.95/1.24  fof(f5292,plain,(
% 6.95/1.24    ( ! [X1] : (sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | (~spl18_120 | ~spl18_282)),
% 6.95/1.24    inference(superposition,[],[f5221,f1756])).
% 6.95/1.24  fof(f5221,plain,(
% 6.95/1.24    ( ! [X0] : (sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl18_282),
% 6.95/1.24    inference(avatar_component_clause,[],[f5220])).
% 6.95/1.24  fof(f7660,plain,(
% 6.95/1.24    spl18_386 | spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_369),
% 6.95/1.24    inference(avatar_split_clause,[],[f7578,f7183,f427,f213,f208,f198,f7658])).
% 6.95/1.24  fof(f208,plain,(
% 6.95/1.24    spl18_3 <=> v4_lattice3(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).
% 6.95/1.24  fof(f427,plain,(
% 6.95/1.24    spl18_24 <=> ! [X3] : m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).
% 6.95/1.24  fof(f7183,plain,(
% 6.95/1.24    spl18_369 <=> ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_369])])).
% 6.95/1.24  fof(f7578,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_369)),
% 6.95/1.24    inference(backward_demodulation,[],[f428,f7502])).
% 6.95/1.24  fof(f7502,plain,(
% 6.95/1.24    ( ! [X13] : (sK12(sK0,X13) = k15_lattice3(sK0,X13)) ) | (spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_369)),
% 6.95/1.24    inference(subsumption_resolution,[],[f7501,f200])).
% 6.95/1.24  fof(f7501,plain,(
% 6.95/1.24    ( ! [X13] : (sK12(sK0,X13) = k15_lattice3(sK0,X13) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4 | ~spl18_369)),
% 6.95/1.24    inference(subsumption_resolution,[],[f7500,f215])).
% 6.95/1.24  fof(f7500,plain,(
% 6.95/1.24    ( ! [X13] : (sK12(sK0,X13) = k15_lattice3(sK0,X13) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_369)),
% 6.95/1.24    inference(subsumption_resolution,[],[f7485,f210])).
% 6.95/1.24  fof(f210,plain,(
% 6.95/1.24    v4_lattice3(sK0) | ~spl18_3),
% 6.95/1.24    inference(avatar_component_clause,[],[f208])).
% 6.95/1.24  fof(f7485,plain,(
% 6.95/1.24    ( ! [X13] : (sK12(sK0,X13) = k15_lattice3(sK0,X13) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_369),
% 6.95/1.24    inference(resolution,[],[f7184,f156])).
% 6.95/1.24  fof(f156,plain,(
% 6.95/1.24    ( ! [X4,X0] : (r4_lattice3(X0,sK12(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f91])).
% 6.95/1.24  fof(f91,plain,(
% 6.95/1.24    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK11(X0,X2)) & r4_lattice3(X0,sK11(X0,X2),sK10(X0)) & m1_subset_1(sK11(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK10(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK12(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK12(X0,X4),X4) & m1_subset_1(sK12(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f87,f90,f89,f88])).
% 6.95/1.24  fof(f88,plain,(
% 6.95/1.24    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK10(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK10(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f89,plain,(
% 6.95/1.24    ! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK10(X0)) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK11(X0,X2)) & r4_lattice3(X0,sK11(X0,X2),sK10(X0)) & m1_subset_1(sK11(X0,X2),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f90,plain,(
% 6.95/1.24    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK12(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK12(X0,X4),X4) & m1_subset_1(sK12(X0,X4),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f87,plain,(
% 6.95/1.24    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f86])).
% 6.95/1.24  fof(f86,plain,(
% 6.95/1.24    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f46])).
% 6.95/1.24  fof(f46,plain,(
% 6.95/1.24    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f45])).
% 6.95/1.24  fof(f45,plain,(
% 6.95/1.24    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f12])).
% 6.95/1.24  fof(f12,axiom,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).
% 6.95/1.24  fof(f7184,plain,(
% 6.95/1.24    ( ! [X8] : (~r4_lattice3(sK0,sK12(sK0,X8),X8) | k15_lattice3(sK0,X8) = sK12(sK0,X8)) ) | ~spl18_369),
% 6.95/1.24    inference(avatar_component_clause,[],[f7183])).
% 6.95/1.24  fof(f428,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))) ) | ~spl18_24),
% 6.95/1.24    inference(avatar_component_clause,[],[f427])).
% 6.95/1.24  fof(f7641,plain,(
% 6.95/1.24    spl18_385 | spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_369),
% 6.95/1.24    inference(avatar_split_clause,[],[f7502,f7183,f213,f208,f198,f7639])).
% 6.95/1.24  fof(f7185,plain,(
% 6.95/1.24    spl18_369 | spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_270),
% 6.95/1.24    inference(avatar_split_clause,[],[f5201,f4640,f427,f213,f208,f203,f198,f7183])).
% 6.95/1.24  fof(f203,plain,(
% 6.95/1.24    spl18_2 <=> v10_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).
% 6.95/1.24  fof(f4640,plain,(
% 6.95/1.24    spl18_270 <=> ! [X1,X0] : (~r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1) | k15_lattice3(sK0,X0) = sK12(sK0,X1) | ~r4_lattice3(sK0,sK12(sK0,X1),X0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_270])])).
% 6.95/1.24  fof(f5201,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8)) ) | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_270)),
% 6.95/1.24    inference(subsumption_resolution,[],[f5200,f200])).
% 6.95/1.24  fof(f5200,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | v2_struct_0(sK0)) ) | (~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_270)),
% 6.95/1.24    inference(subsumption_resolution,[],[f5199,f205])).
% 6.95/1.24  fof(f205,plain,(
% 6.95/1.24    v10_lattices(sK0) | ~spl18_2),
% 6.95/1.24    inference(avatar_component_clause,[],[f203])).
% 6.95/1.24  fof(f5199,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_270)),
% 6.95/1.24    inference(subsumption_resolution,[],[f5198,f210])).
% 6.95/1.24  fof(f5198,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_24 | ~spl18_270)),
% 6.95/1.24    inference(subsumption_resolution,[],[f5197,f215])).
% 6.95/1.24  fof(f5197,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_24 | ~spl18_270)),
% 6.95/1.24    inference(subsumption_resolution,[],[f5196,f428])).
% 6.95/1.24  fof(f5196,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | ~m1_subset_1(sK12(sK0,X8),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_270),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f5194])).
% 6.95/1.24  fof(f5194,plain,(
% 6.95/1.24    ( ! [X8] : (k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | k15_lattice3(sK0,X8) = sK12(sK0,X8) | ~r4_lattice3(sK0,sK12(sK0,X8),X8) | ~m1_subset_1(sK12(sK0,X8),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_270),
% 6.95/1.24    inference(resolution,[],[f4641,f195])).
% 6.95/1.24  fof(f195,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (r4_lattice3(X0,sK7(X0,X1,X2),X1) | k15_lattice3(X0,X1) = X2 | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f149])).
% 6.95/1.24  fof(f149,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK7(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f80])).
% 6.95/1.24  fof(f80,plain,(
% 6.95/1.24    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f78,f79])).
% 6.95/1.24  fof(f79,plain,(
% 6.95/1.24    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f78,plain,(
% 6.95/1.24    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f77])).
% 6.95/1.24  fof(f77,plain,(
% 6.95/1.24    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f76])).
% 6.95/1.24  fof(f76,plain,(
% 6.95/1.24    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f42])).
% 6.95/1.24  fof(f42,plain,(
% 6.95/1.24    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f41])).
% 6.95/1.24  fof(f41,plain,(
% 6.95/1.24    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f13])).
% 6.95/1.24  fof(f13,axiom,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 6.95/1.24  fof(f4641,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1) | k15_lattice3(sK0,X0) = sK12(sK0,X1) | ~r4_lattice3(sK0,sK12(sK0,X1),X0)) ) | ~spl18_270),
% 6.95/1.24    inference(avatar_component_clause,[],[f4640])).
% 6.95/1.24  fof(f6437,plain,(
% 6.95/1.24    spl18_197 | ~spl18_13 | ~spl18_272),
% 6.95/1.24    inference(avatar_split_clause,[],[f4811,f4660,f339,f3063])).
% 6.95/1.24  fof(f3063,plain,(
% 6.95/1.24    spl18_197 <=> k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_197])])).
% 6.95/1.24  fof(f339,plain,(
% 6.95/1.24    spl18_13 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).
% 6.95/1.24  fof(f4660,plain,(
% 6.95/1.24    spl18_272 <=> ! [X0] : (k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_272])])).
% 6.95/1.24  fof(f4811,plain,(
% 6.95/1.24    k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl18_13 | ~spl18_272)),
% 6.95/1.24    inference(resolution,[],[f4661,f341])).
% 6.95/1.24  fof(f341,plain,(
% 6.95/1.24    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl18_13),
% 6.95/1.24    inference(avatar_component_clause,[],[f339])).
% 6.95/1.24  fof(f4661,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0) ) | ~spl18_272),
% 6.95/1.24    inference(avatar_component_clause,[],[f4660])).
% 6.95/1.24  fof(f5524,plain,(
% 6.95/1.24    spl18_302 | ~spl18_187 | ~spl18_285),
% 6.95/1.24    inference(avatar_split_clause,[],[f5336,f5237,f2768,f5522])).
% 6.95/1.24  fof(f2768,plain,(
% 6.95/1.24    spl18_187 <=> ! [X11,X12] : k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_187])])).
% 6.95/1.24  fof(f5237,plain,(
% 6.95/1.24    spl18_285 <=> ! [X22] : k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_285])])).
% 6.95/1.24  fof(f5336,plain,(
% 6.95/1.24    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (~spl18_187 | ~spl18_285)),
% 6.95/1.24    inference(superposition,[],[f2769,f5238])).
% 6.95/1.24  fof(f5238,plain,(
% 6.95/1.24    ( ! [X22] : (k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))) ) | ~spl18_285),
% 6.95/1.24    inference(avatar_component_clause,[],[f5237])).
% 6.95/1.24  fof(f2769,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))) ) | ~spl18_187),
% 6.95/1.24    inference(avatar_component_clause,[],[f2768])).
% 6.95/1.24  fof(f5239,plain,(
% 6.95/1.24    spl18_285 | spl18_1 | ~spl18_4 | ~spl18_272),
% 6.95/1.24    inference(avatar_split_clause,[],[f4844,f4660,f213,f198,f5237])).
% 6.95/1.24  fof(f4844,plain,(
% 6.95/1.24    ( ! [X22] : (k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22))) ) | (spl18_1 | ~spl18_4 | ~spl18_272)),
% 6.95/1.24    inference(subsumption_resolution,[],[f4843,f200])).
% 6.95/1.24  fof(f4843,plain,(
% 6.95/1.24    ( ! [X22] : (k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_272)),
% 6.95/1.24    inference(subsumption_resolution,[],[f4833,f215])).
% 6.95/1.24  fof(f4833,plain,(
% 6.95/1.24    ( ! [X22] : (k15_lattice3(sK0,X22) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X22)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_272),
% 6.95/1.24    inference(resolution,[],[f4661,f170])).
% 6.95/1.24  fof(f5222,plain,(
% 6.95/1.24    spl18_282 | ~spl18_85 | ~spl18_189),
% 6.95/1.24    inference(avatar_split_clause,[],[f4649,f2778,f1407,f5220])).
% 6.95/1.24  fof(f1407,plain,(
% 6.95/1.24    spl18_85 <=> ! [X5] : k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_85])])).
% 6.95/1.24  fof(f2778,plain,(
% 6.95/1.24    spl18_189 <=> ! [X11,X12] : sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_189])])).
% 6.95/1.24  fof(f4649,plain,(
% 6.95/1.24    ( ! [X0] : (sK12(sK0,k1_xboole_0) = k2_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (~spl18_85 | ~spl18_189)),
% 6.95/1.24    inference(superposition,[],[f2779,f1408])).
% 6.95/1.24  fof(f1408,plain,(
% 6.95/1.24    ( ! [X5] : (k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))) ) | ~spl18_85),
% 6.95/1.24    inference(avatar_component_clause,[],[f1407])).
% 6.95/1.24  fof(f2779,plain,(
% 6.95/1.24    ( ! [X12,X11] : (sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))) ) | ~spl18_189),
% 6.95/1.24    inference(avatar_component_clause,[],[f2778])).
% 6.95/1.24  fof(f4662,plain,(
% 6.95/1.24    spl18_272 | ~spl18_28 | ~spl18_175),
% 6.95/1.24    inference(avatar_split_clause,[],[f2695,f2473,f484,f4660])).
% 6.95/1.24  fof(f484,plain,(
% 6.95/1.24    spl18_28 <=> ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | r4_lattice3(sK0,X16,k1_xboole_0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_28])])).
% 6.95/1.24  fof(f2473,plain,(
% 6.95/1.24    spl18_175 <=> ! [X1,X0] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_175])])).
% 6.95/1.24  fof(f2695,plain,(
% 6.95/1.24    ( ! [X0] : (k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl18_28 | ~spl18_175)),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f2678])).
% 6.95/1.24  fof(f2678,plain,(
% 6.95/1.24    ( ! [X0] : (k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl18_28 | ~spl18_175)),
% 6.95/1.24    inference(resolution,[],[f2474,f485])).
% 6.95/1.24  fof(f485,plain,(
% 6.95/1.24    ( ! [X16] : (r4_lattice3(sK0,X16,k1_xboole_0) | ~m1_subset_1(X16,u1_struct_0(sK0))) ) | ~spl18_28),
% 6.95/1.24    inference(avatar_component_clause,[],[f484])).
% 6.95/1.24  fof(f2474,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl18_175),
% 6.95/1.24    inference(avatar_component_clause,[],[f2473])).
% 6.95/1.24  fof(f4642,plain,(
% 6.95/1.24    spl18_270 | ~spl18_24 | ~spl18_38 | ~spl18_132),
% 6.95/1.24    inference(avatar_split_clause,[],[f2003,f1994,f650,f427,f4640])).
% 6.95/1.24  fof(f650,plain,(
% 6.95/1.24    spl18_38 <=> ! [X1,X0] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = X1)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_38])])).
% 6.95/1.24  fof(f1994,plain,(
% 6.95/1.24    spl18_132 <=> ! [X3,X2] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_132])])).
% 6.95/1.24  fof(f2003,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1) | k15_lattice3(sK0,X0) = sK12(sK0,X1) | ~r4_lattice3(sK0,sK12(sK0,X1),X0)) ) | (~spl18_24 | ~spl18_38 | ~spl18_132)),
% 6.95/1.24    inference(subsumption_resolution,[],[f2002,f428])).
% 6.95/1.24  fof(f2002,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1) | k15_lattice3(sK0,X0) = sK12(sK0,X1) | ~r4_lattice3(sK0,sK12(sK0,X1),X0) | ~m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0))) ) | (~spl18_38 | ~spl18_132)),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f2001])).
% 6.95/1.24  fof(f2001,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,sK7(sK0,X0,sK12(sK0,X1)),X1) | k15_lattice3(sK0,X0) = sK12(sK0,X1) | ~r4_lattice3(sK0,sK12(sK0,X1),X0) | ~r4_lattice3(sK0,sK12(sK0,X1),X0) | ~m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = sK12(sK0,X1)) ) | (~spl18_38 | ~spl18_132)),
% 6.95/1.24    inference(resolution,[],[f1995,f651])).
% 6.95/1.24  fof(f651,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = X1) ) | ~spl18_38),
% 6.95/1.24    inference(avatar_component_clause,[],[f650])).
% 6.95/1.24  fof(f1995,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2)) ) | ~spl18_132),
% 6.95/1.24    inference(avatar_component_clause,[],[f1994])).
% 6.95/1.24  fof(f3273,plain,(
% 6.95/1.24    spl18_6 | ~spl18_168 | ~spl18_172 | ~spl18_197),
% 6.95/1.24    inference(avatar_split_clause,[],[f3254,f3063,f2459,f2436,f229])).
% 6.95/1.24  fof(f229,plain,(
% 6.95/1.24    spl18_6 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).
% 6.95/1.24  fof(f2436,plain,(
% 6.95/1.24    spl18_168 <=> ! [X11] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_168])])).
% 6.95/1.24  fof(f2459,plain,(
% 6.95/1.24    spl18_172 <=> ! [X10] : k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_172])])).
% 6.95/1.24  fof(f3254,plain,(
% 6.95/1.24    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (~spl18_168 | ~spl18_172 | ~spl18_197)),
% 6.95/1.24    inference(forward_demodulation,[],[f3251,f2437])).
% 6.95/1.24  fof(f2437,plain,(
% 6.95/1.24    ( ! [X11] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))) ) | ~spl18_168),
% 6.95/1.24    inference(avatar_component_clause,[],[f2436])).
% 6.95/1.24  fof(f3251,plain,(
% 6.95/1.24    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl18_172 | ~spl18_197)),
% 6.95/1.24    inference(superposition,[],[f2460,f3065])).
% 6.95/1.24  fof(f3065,plain,(
% 6.95/1.24    k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl18_197),
% 6.95/1.24    inference(avatar_component_clause,[],[f3063])).
% 6.95/1.24  fof(f2460,plain,(
% 6.95/1.24    ( ! [X10] : (k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))) ) | ~spl18_172),
% 6.95/1.24    inference(avatar_component_clause,[],[f2459])).
% 6.95/1.24  fof(f2780,plain,(
% 6.95/1.24    spl18_189 | spl18_1 | ~spl18_4 | ~spl18_74),
% 6.95/1.24    inference(avatar_split_clause,[],[f1361,f1285,f213,f198,f2778])).
% 6.95/1.24  fof(f1285,plain,(
% 6.95/1.24    spl18_74 <=> ! [X16,X17] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_74])])).
% 6.95/1.24  fof(f1361,plain,(
% 6.95/1.24    ( ! [X12,X11] : (sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12)))) ) | (spl18_1 | ~spl18_4 | ~spl18_74)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1360,f200])).
% 6.95/1.24  fof(f1360,plain,(
% 6.95/1.24    ( ! [X12,X11] : (sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12))) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_74)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1348,f215])).
% 6.95/1.24  fof(f1348,plain,(
% 6.95/1.24    ( ! [X12,X11] : (sK12(sK0,X11) = k2_lattices(sK0,sK12(sK0,X11),k1_lattices(sK0,sK12(sK0,X11),k15_lattice3(sK0,X12))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_74),
% 6.95/1.24    inference(resolution,[],[f1286,f170])).
% 6.95/1.24  fof(f1286,plain,(
% 6.95/1.24    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16))) ) | ~spl18_74),
% 6.95/1.24    inference(avatar_component_clause,[],[f1285])).
% 6.95/1.24  fof(f2770,plain,(
% 6.95/1.24    spl18_187 | spl18_1 | ~spl18_4 | ~spl18_73),
% 6.95/1.24    inference(avatar_split_clause,[],[f1327,f1275,f213,f198,f2768])).
% 6.95/1.24  fof(f1275,plain,(
% 6.95/1.24    spl18_73 <=> ! [X7,X8] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_73])])).
% 6.95/1.24  fof(f1327,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12)))) ) | (spl18_1 | ~spl18_4 | ~spl18_73)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1326,f200])).
% 6.95/1.24  fof(f1326,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12))) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_73)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1314,f215])).
% 6.95/1.24  fof(f1314,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k15_lattice3(sK0,X11) = k2_lattices(sK0,k15_lattice3(sK0,X11),k1_lattices(sK0,k15_lattice3(sK0,X11),k15_lattice3(sK0,X12))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_73),
% 6.95/1.24    inference(resolution,[],[f1276,f170])).
% 6.95/1.24  fof(f1276,plain,(
% 6.95/1.24    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7))) ) | ~spl18_73),
% 6.95/1.24    inference(avatar_component_clause,[],[f1275])).
% 6.95/1.24  fof(f2755,plain,(
% 6.95/1.24    spl18_184 | spl18_1 | ~spl18_4 | ~spl18_50),
% 6.95/1.24    inference(avatar_split_clause,[],[f1158,f848,f213,f198,f2753])).
% 6.95/1.24  fof(f848,plain,(
% 6.95/1.24    spl18_50 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_50])])).
% 6.95/1.24  fof(f1158,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11)) | ~m1_subset_1(X12,u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_4 | ~spl18_50)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1157,f200])).
% 6.95/1.24  fof(f1157,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_50)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1145,f215])).
% 6.95/1.24  fof(f1145,plain,(
% 6.95/1.24    ( ! [X12,X11] : (k2_lattices(sK0,k15_lattice3(sK0,X11),X12) = k2_lattices(sK0,X12,k15_lattice3(sK0,X11)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_50),
% 6.95/1.24    inference(resolution,[],[f849,f170])).
% 6.95/1.24  fof(f849,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl18_50),
% 6.95/1.24    inference(avatar_component_clause,[],[f848])).
% 6.95/1.24  fof(f2475,plain,(
% 6.95/1.24    spl18_175 | spl18_1 | ~spl18_4 | ~spl18_88),
% 6.95/1.24    inference(avatar_split_clause,[],[f1465,f1451,f213,f198,f2473])).
% 6.95/1.24  fof(f1451,plain,(
% 6.95/1.24    spl18_88 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_88])])).
% 6.95/1.24  fof(f1465,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_4 | ~spl18_88)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1464,f200])).
% 6.95/1.24  fof(f1464,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_88)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1459,f215])).
% 6.95/1.24  fof(f1459,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_88),
% 6.95/1.24    inference(resolution,[],[f1452,f170])).
% 6.95/1.24  fof(f1452,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl18_88),
% 6.95/1.24    inference(avatar_component_clause,[],[f1451])).
% 6.95/1.24  fof(f2461,plain,(
% 6.95/1.24    spl18_172 | spl18_1 | ~spl18_11 | ~spl18_73),
% 6.95/1.24    inference(avatar_split_clause,[],[f1325,f1275,f320,f198,f2459])).
% 6.95/1.24  fof(f1325,plain,(
% 6.95/1.24    ( ! [X10] : (k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0)))) ) | (spl18_1 | ~spl18_11 | ~spl18_73)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1324,f200])).
% 6.95/1.24  fof(f1324,plain,(
% 6.95/1.24    ( ! [X10] : (k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl18_11 | ~spl18_73)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1313,f321])).
% 6.95/1.24  fof(f1313,plain,(
% 6.95/1.24    ( ! [X10] : (k15_lattice3(sK0,X10) = k2_lattices(sK0,k15_lattice3(sK0,X10),k1_lattices(sK0,k15_lattice3(sK0,X10),k5_lattices(sK0))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_73),
% 6.95/1.24    inference(resolution,[],[f1276,f127])).
% 6.95/1.24  fof(f127,plain,(
% 6.95/1.24    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f30])).
% 6.95/1.24  fof(f30,plain,(
% 6.95/1.24    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f29])).
% 6.95/1.24  fof(f29,plain,(
% 6.95/1.24    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f7])).
% 6.95/1.24  fof(f7,axiom,(
% 6.95/1.24    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 6.95/1.24  fof(f2438,plain,(
% 6.95/1.24    spl18_168 | spl18_1 | ~spl18_4 | ~spl18_56 | ~spl18_124),
% 6.95/1.24    inference(avatar_split_clause,[],[f2415,f1771,f1014,f213,f198,f2436])).
% 6.95/1.24  fof(f1014,plain,(
% 6.95/1.24    spl18_56 <=> ! [X5] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_56])])).
% 6.95/1.24  fof(f1771,plain,(
% 6.95/1.24    spl18_124 <=> ! [X10] : (k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_124])])).
% 6.95/1.24  fof(f2415,plain,(
% 6.95/1.24    ( ! [X11] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))) ) | (spl18_1 | ~spl18_4 | ~spl18_56 | ~spl18_124)),
% 6.95/1.24    inference(forward_demodulation,[],[f2414,f1015])).
% 6.95/1.24  fof(f1015,plain,(
% 6.95/1.24    ( ! [X5] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))) ) | ~spl18_56),
% 6.95/1.24    inference(avatar_component_clause,[],[f1014])).
% 6.95/1.24  fof(f2414,plain,(
% 6.95/1.24    ( ! [X11] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0))) ) | (spl18_1 | ~spl18_4 | ~spl18_124)),
% 6.95/1.24    inference(subsumption_resolution,[],[f2413,f200])).
% 6.95/1.24  fof(f2413,plain,(
% 6.95/1.24    ( ! [X11] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_124)),
% 6.95/1.24    inference(subsumption_resolution,[],[f2396,f215])).
% 6.95/1.24  fof(f2396,plain,(
% 6.95/1.24    ( ! [X11] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X11)) = k2_lattices(sK0,k15_lattice3(sK0,X11),k5_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_124),
% 6.95/1.24    inference(resolution,[],[f1772,f170])).
% 6.95/1.24  fof(f1772,plain,(
% 6.95/1.24    ( ! [X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0))) ) | ~spl18_124),
% 6.95/1.24    inference(avatar_component_clause,[],[f1771])).
% 6.95/1.24  fof(f1996,plain,(
% 6.95/1.24    spl18_132 | spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_27),
% 6.95/1.24    inference(avatar_split_clause,[],[f510,f480,f427,f213,f208,f203,f198,f1994])).
% 6.95/1.24  fof(f480,plain,(
% 6.95/1.24    spl18_27 <=> ! [X1,X0] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK12(sK0,X1),X0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_27])])).
% 6.95/1.24  fof(f510,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2)) ) | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f509,f200])).
% 6.95/1.24  fof(f509,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2) | v2_struct_0(sK0)) ) | (~spl18_2 | ~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f508,f205])).
% 6.95/1.24  fof(f508,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4 | ~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f507,f210])).
% 6.95/1.24  fof(f507,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f506,f215])).
% 6.95/1.24  fof(f506,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f500,f428])).
% 6.95/1.24  fof(f500,plain,(
% 6.95/1.24    ( ! [X2,X3] : (~m1_subset_1(sK7(sK0,X2,sK12(sK0,X3)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK7(sK0,X2,sK12(sK0,X3)),X3) | k15_lattice3(sK0,X2) = sK12(sK0,X3) | ~r4_lattice3(sK0,sK12(sK0,X3),X2) | ~m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_27),
% 6.95/1.24    inference(resolution,[],[f481,f196])).
% 6.95/1.24  fof(f196,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,sK7(X0,X1,X2)) | k15_lattice3(X0,X1) = X2 | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f150])).
% 6.95/1.24  fof(f150,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK7(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f80])).
% 6.95/1.24  fof(f481,plain,(
% 6.95/1.24    ( ! [X0,X1] : (r1_lattices(sK0,sK12(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1)) ) | ~spl18_27),
% 6.95/1.24    inference(avatar_component_clause,[],[f480])).
% 6.95/1.24  fof(f1773,plain,(
% 6.95/1.24    spl18_124 | spl18_1 | ~spl18_11 | ~spl18_50),
% 6.95/1.24    inference(avatar_split_clause,[],[f1156,f848,f320,f198,f1771])).
% 6.95/1.24  fof(f1156,plain,(
% 6.95/1.24    ( ! [X10] : (k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_11 | ~spl18_50)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1155,f200])).
% 6.95/1.24  fof(f1155,plain,(
% 6.95/1.24    ( ! [X10] : (k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl18_11 | ~spl18_50)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1144,f321])).
% 6.95/1.24  fof(f1144,plain,(
% 6.95/1.24    ( ! [X10] : (k2_lattices(sK0,k5_lattices(sK0),X10) = k2_lattices(sK0,X10,k5_lattices(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_50),
% 6.95/1.24    inference(resolution,[],[f849,f127])).
% 6.95/1.24  fof(f1757,plain,(
% 6.95/1.24    spl18_120 | spl18_1 | ~spl18_4 | ~spl18_47),
% 6.95/1.24    inference(avatar_split_clause,[],[f1042,f764,f213,f198,f1755])).
% 6.95/1.24  fof(f764,plain,(
% 6.95/1.24    spl18_47 <=> ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_47])])).
% 6.95/1.24  fof(f1042,plain,(
% 6.95/1.24    ( ! [X5] : (sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5))))) ) | (spl18_1 | ~spl18_4 | ~spl18_47)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1041,f200])).
% 6.95/1.24  fof(f1041,plain,(
% 6.95/1.24    ( ! [X5] : (sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5)))) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_47)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1029,f215])).
% 6.95/1.24  fof(f1029,plain,(
% 6.95/1.24    ( ! [X5] : (sK2(sK0,k15_lattice3(sK0,X5)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X5)))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_47),
% 6.95/1.24    inference(resolution,[],[f765,f170])).
% 6.95/1.24  fof(f765,plain,(
% 6.95/1.24    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))) ) | ~spl18_47),
% 6.95/1.24    inference(avatar_component_clause,[],[f764])).
% 6.95/1.24  fof(f1453,plain,(
% 6.95/1.24    spl18_88 | spl18_1 | ~spl18_30 | ~spl18_66),
% 6.95/1.24    inference(avatar_split_clause,[],[f1440,f1178,f492,f198,f1451])).
% 6.95/1.24  fof(f492,plain,(
% 6.95/1.24    spl18_30 <=> ! [X1,X0] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_30])])).
% 6.95/1.24  fof(f1178,plain,(
% 6.95/1.24    spl18_66 <=> l2_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_66])])).
% 6.95/1.24  fof(f1440,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_30 | ~spl18_66)),
% 6.95/1.24    inference(subsumption_resolution,[],[f553,f1179])).
% 6.95/1.24  fof(f1179,plain,(
% 6.95/1.24    l2_lattices(sK0) | ~spl18_66),
% 6.95/1.24    inference(avatar_component_clause,[],[f1178])).
% 6.95/1.24  fof(f553,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0)) ) | (spl18_1 | ~spl18_30)),
% 6.95/1.24    inference(subsumption_resolution,[],[f552,f200])).
% 6.95/1.24  fof(f552,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_30),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f545])).
% 6.95/1.24  fof(f545,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_30),
% 6.95/1.24    inference(resolution,[],[f493,f125])).
% 6.95/1.24  fof(f125,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f59])).
% 6.95/1.24  fof(f59,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f28])).
% 6.95/1.24  fof(f28,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f27])).
% 6.95/1.24  fof(f27,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f5])).
% 6.95/1.24  fof(f5,axiom,(
% 6.95/1.24    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 6.95/1.24  fof(f493,plain,(
% 6.95/1.24    ( ! [X0,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1)) ) | ~spl18_30),
% 6.95/1.24    inference(avatar_component_clause,[],[f492])).
% 6.95/1.24  fof(f1409,plain,(
% 6.95/1.24    spl18_85 | spl18_1 | ~spl18_4 | ~spl18_70),
% 6.95/1.24    inference(avatar_split_clause,[],[f1249,f1223,f213,f198,f1407])).
% 6.95/1.24  fof(f1223,plain,(
% 6.95/1.24    spl18_70 <=> ! [X0] : (k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).
% 6.95/1.24  fof(f1249,plain,(
% 6.95/1.24    ( ! [X5] : (k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5))) ) | (spl18_1 | ~spl18_4 | ~spl18_70)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1248,f200])).
% 6.95/1.24  fof(f1248,plain,(
% 6.95/1.24    ( ! [X5] : (k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_70)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1236,f215])).
% 6.95/1.24  fof(f1236,plain,(
% 6.95/1.24    ( ! [X5] : (k15_lattice3(sK0,X5) = k1_lattices(sK0,sK12(sK0,k1_xboole_0),k15_lattice3(sK0,X5)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_70),
% 6.95/1.24    inference(resolution,[],[f1224,f170])).
% 6.95/1.24  fof(f1224,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0) ) | ~spl18_70),
% 6.95/1.24    inference(avatar_component_clause,[],[f1223])).
% 6.95/1.24  fof(f1287,plain,(
% 6.95/1.24    spl18_74 | spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_37),
% 6.95/1.24    inference(avatar_split_clause,[],[f631,f589,f213,f208,f198,f1285])).
% 6.95/1.24  fof(f589,plain,(
% 6.95/1.24    spl18_37 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_37])])).
% 6.95/1.24  fof(f631,plain,(
% 6.95/1.24    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16))) ) | (spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_37)),
% 6.95/1.24    inference(subsumption_resolution,[],[f630,f200])).
% 6.95/1.24  fof(f630,plain,(
% 6.95/1.24    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4 | ~spl18_37)),
% 6.95/1.24    inference(subsumption_resolution,[],[f629,f215])).
% 6.95/1.24  fof(f629,plain,(
% 6.95/1.24    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_37)),
% 6.95/1.24    inference(subsumption_resolution,[],[f611,f210])).
% 6.95/1.24  fof(f611,plain,(
% 6.95/1.24    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | sK12(sK0,X17) = k2_lattices(sK0,sK12(sK0,X17),k1_lattices(sK0,sK12(sK0,X17),X16)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_37),
% 6.95/1.24    inference(resolution,[],[f590,f155])).
% 6.95/1.24  fof(f155,plain,(
% 6.95/1.24    ( ! [X4,X0] : (m1_subset_1(sK12(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f91])).
% 6.95/1.24  fof(f590,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1) ) | ~spl18_37),
% 6.95/1.24    inference(avatar_component_clause,[],[f589])).
% 6.95/1.24  fof(f1277,plain,(
% 6.95/1.24    spl18_73 | spl18_1 | ~spl18_4 | ~spl18_37),
% 6.95/1.24    inference(avatar_split_clause,[],[f617,f589,f213,f198,f1275])).
% 6.95/1.24  fof(f617,plain,(
% 6.95/1.24    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7))) ) | (spl18_1 | ~spl18_4 | ~spl18_37)),
% 6.95/1.24    inference(subsumption_resolution,[],[f616,f200])).
% 6.95/1.24  fof(f616,plain,(
% 6.95/1.24    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_37)),
% 6.95/1.24    inference(subsumption_resolution,[],[f604,f215])).
% 6.95/1.24  fof(f604,plain,(
% 6.95/1.24    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k15_lattice3(sK0,X8) = k2_lattices(sK0,k15_lattice3(sK0,X8),k1_lattices(sK0,k15_lattice3(sK0,X8),X7)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_37),
% 6.95/1.24    inference(resolution,[],[f590,f170])).
% 6.95/1.24  fof(f1225,plain,(
% 6.95/1.24    spl18_70 | ~spl18_28 | ~spl18_67),
% 6.95/1.24    inference(avatar_split_clause,[],[f1202,f1182,f484,f1223])).
% 6.95/1.24  fof(f1182,plain,(
% 6.95/1.24    spl18_67 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~r4_lattice3(sK0,X0,X1))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_67])])).
% 6.95/1.24  fof(f1202,plain,(
% 6.95/1.24    ( ! [X0] : (k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl18_28 | ~spl18_67)),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f1194])).
% 6.95/1.24  fof(f1194,plain,(
% 6.95/1.24    ( ! [X0] : (k1_lattices(sK0,sK12(sK0,k1_xboole_0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl18_28 | ~spl18_67)),
% 6.95/1.24    inference(resolution,[],[f1183,f485])).
% 6.95/1.24  fof(f1183,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl18_67),
% 6.95/1.24    inference(avatar_component_clause,[],[f1182])).
% 6.95/1.24  fof(f1189,plain,(
% 6.95/1.24    ~spl18_4 | spl18_66),
% 6.95/1.24    inference(avatar_contradiction_clause,[],[f1188])).
% 6.95/1.24  fof(f1188,plain,(
% 6.95/1.24    $false | (~spl18_4 | spl18_66)),
% 6.95/1.24    inference(subsumption_resolution,[],[f1186,f215])).
% 6.95/1.24  fof(f1186,plain,(
% 6.95/1.24    ~l3_lattices(sK0) | spl18_66),
% 6.95/1.24    inference(resolution,[],[f1180,f117])).
% 6.95/1.24  fof(f117,plain,(
% 6.95/1.24    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f24])).
% 6.95/1.24  fof(f24,plain,(
% 6.95/1.24    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 6.95/1.24    inference(ennf_transformation,[],[f8])).
% 6.95/1.24  fof(f8,axiom,(
% 6.95/1.24    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 6.95/1.24  fof(f1180,plain,(
% 6.95/1.24    ~l2_lattices(sK0) | spl18_66),
% 6.95/1.24    inference(avatar_component_clause,[],[f1178])).
% 6.95/1.24  fof(f1184,plain,(
% 6.95/1.24    ~spl18_66 | spl18_67 | spl18_1 | ~spl18_24 | ~spl18_27),
% 6.95/1.24    inference(avatar_split_clause,[],[f505,f480,f427,f198,f1182,f1178])).
% 6.95/1.24  fof(f505,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~l2_lattices(sK0)) ) | (spl18_1 | ~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f504,f200])).
% 6.95/1.24  fof(f504,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_24 | ~spl18_27)),
% 6.95/1.24    inference(subsumption_resolution,[],[f503,f428])).
% 6.95/1.24  fof(f503,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_27),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f499])).
% 6.95/1.24  fof(f499,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,sK12(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK12(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_27),
% 6.95/1.24    inference(resolution,[],[f481,f125])).
% 6.95/1.24  fof(f1016,plain,(
% 6.95/1.24    spl18_56 | spl18_1 | ~spl18_4 | ~spl18_48),
% 6.95/1.24    inference(avatar_split_clause,[],[f993,f807,f213,f198,f1014])).
% 6.95/1.24  fof(f807,plain,(
% 6.95/1.24    spl18_48 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_48])])).
% 6.95/1.24  fof(f993,plain,(
% 6.95/1.24    ( ! [X5] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5))) ) | (spl18_1 | ~spl18_4 | ~spl18_48)),
% 6.95/1.24    inference(subsumption_resolution,[],[f992,f200])).
% 6.95/1.24  fof(f992,plain,(
% 6.95/1.24    ( ! [X5] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_48)),
% 6.95/1.24    inference(subsumption_resolution,[],[f982,f215])).
% 6.95/1.24  fof(f982,plain,(
% 6.95/1.24    ( ! [X5] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X5)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_48),
% 6.95/1.24    inference(resolution,[],[f808,f170])).
% 6.95/1.24  fof(f808,plain,(
% 6.95/1.24    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)) ) | ~spl18_48),
% 6.95/1.24    inference(avatar_component_clause,[],[f807])).
% 6.95/1.24  fof(f850,plain,(
% 6.95/1.24    spl18_50 | spl18_1 | ~spl18_2 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f663,f213,f203,f198,f848])).
% 6.95/1.24  fof(f663,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_2 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f662,f215])).
% 6.95/1.24  fof(f662,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) ) | (spl18_1 | ~spl18_2)),
% 6.95/1.24    inference(subsumption_resolution,[],[f661,f200])).
% 6.95/1.24  fof(f661,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) ) | ~spl18_2),
% 6.95/1.24    inference(resolution,[],[f392,f205])).
% 6.95/1.24  fof(f392,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1)) )),
% 6.95/1.24    inference(subsumption_resolution,[],[f391,f116])).
% 6.95/1.24  fof(f116,plain,(
% 6.95/1.24    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f24])).
% 6.95/1.24  fof(f391,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1)) )),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f390])).
% 6.95/1.24  fof(f390,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 6.95/1.24    inference(resolution,[],[f137,f121])).
% 6.95/1.24  fof(f121,plain,(
% 6.95/1.24    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f26])).
% 6.95/1.24  fof(f26,plain,(
% 6.95/1.24    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 6.95/1.24    inference(flattening,[],[f25])).
% 6.95/1.24  fof(f25,plain,(
% 6.95/1.24    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 6.95/1.24    inference(ennf_transformation,[],[f3])).
% 6.95/1.24  fof(f3,axiom,(
% 6.95/1.24    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 6.95/1.24  fof(f137,plain,(
% 6.95/1.24    ( ! [X4,X0,X3] : (~v6_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f73])).
% 6.95/1.24  fof(f73,plain,(
% 6.95/1.24    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f70,f72,f71])).
% 6.95/1.24  fof(f71,plain,(
% 6.95/1.24    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f72,plain,(
% 6.95/1.24    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f70,plain,(
% 6.95/1.24    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f69])).
% 6.95/1.24  fof(f69,plain,(
% 6.95/1.24    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f36])).
% 6.95/1.24  fof(f36,plain,(
% 6.95/1.24    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f35])).
% 6.95/1.24  fof(f35,plain,(
% 6.95/1.24    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f14])).
% 6.95/1.24  fof(f14,axiom,(
% 6.95/1.24    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 6.95/1.24  fof(f809,plain,(
% 6.95/1.24    spl18_48 | spl18_1 | ~spl18_5 | ~spl18_11),
% 6.95/1.24    inference(avatar_split_clause,[],[f796,f320,f225,f198,f807])).
% 6.95/1.24  fof(f796,plain,(
% 6.95/1.24    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)) ) | (spl18_1 | ~spl18_5 | ~spl18_11)),
% 6.95/1.24    inference(subsumption_resolution,[],[f795,f200])).
% 6.95/1.24  fof(f795,plain,(
% 6.95/1.24    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) | v2_struct_0(sK0)) ) | (~spl18_5 | ~spl18_11)),
% 6.95/1.24    inference(subsumption_resolution,[],[f788,f321])).
% 6.95/1.24  fof(f788,plain,(
% 6.95/1.24    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_5),
% 6.95/1.24    inference(resolution,[],[f226,f419])).
% 6.95/1.24  fof(f419,plain,(
% 6.95/1.24    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(subsumption_resolution,[],[f185,f127])).
% 6.95/1.24  fof(f185,plain,(
% 6.95/1.24    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(equality_resolution,[],[f128])).
% 6.95/1.24  fof(f128,plain,(
% 6.95/1.24    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f63])).
% 6.95/1.24  fof(f63,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f61,f62])).
% 6.95/1.24  fof(f62,plain,(
% 6.95/1.24    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f61,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f60])).
% 6.95/1.24  fof(f60,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f32])).
% 6.95/1.24  fof(f32,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f31])).
% 6.95/1.24  fof(f31,plain,(
% 6.95/1.24    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f4])).
% 6.95/1.24  fof(f4,axiom,(
% 6.95/1.24    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 6.95/1.24  fof(f226,plain,(
% 6.95/1.24    v13_lattices(sK0) | ~spl18_5),
% 6.95/1.24    inference(avatar_component_clause,[],[f225])).
% 6.95/1.24  fof(f766,plain,(
% 6.95/1.24    spl18_47 | spl18_1 | spl18_5 | ~spl18_9 | ~spl18_11),
% 6.95/1.24    inference(avatar_split_clause,[],[f761,f320,f250,f225,f198,f764])).
% 6.95/1.24  fof(f250,plain,(
% 6.95/1.24    spl18_9 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).
% 6.95/1.24  fof(f761,plain,(
% 6.95/1.24    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl18_1 | spl18_5 | ~spl18_9 | ~spl18_11)),
% 6.95/1.24    inference(subsumption_resolution,[],[f271,f321])).
% 6.95/1.24  fof(f271,plain,(
% 6.95/1.24    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0)) ) | (spl18_1 | spl18_5 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f270,f200])).
% 6.95/1.24  fof(f270,plain,(
% 6.95/1.24    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl18_5 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f259,f227])).
% 6.95/1.24  fof(f259,plain,(
% 6.95/1.24    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | v13_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_9),
% 6.95/1.24    inference(resolution,[],[f251,f135])).
% 6.95/1.24  fof(f135,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f68])).
% 6.95/1.24  fof(f251,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0) ) | ~spl18_9),
% 6.95/1.24    inference(avatar_component_clause,[],[f250])).
% 6.95/1.24  fof(f652,plain,(
% 6.95/1.24    spl18_38 | spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f444,f213,f208,f203,f198,f650])).
% 6.95/1.24  fof(f444,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = X1) ) | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f443,f200])).
% 6.95/1.24  fof(f443,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = X1 | v2_struct_0(sK0)) ) | (~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f442,f205])).
% 6.95/1.24  fof(f442,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = X1 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f441,f215])).
% 6.95/1.24  fof(f441,plain,(
% 6.95/1.24    ( ! [X0,X1] : (m1_subset_1(sK7(sK0,X0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,X0) = X1 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_3),
% 6.95/1.24    inference(resolution,[],[f194,f210])).
% 6.95/1.24  fof(f194,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = X2 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f148])).
% 6.95/1.24  fof(f148,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f80])).
% 6.95/1.24  fof(f599,plain,(
% 6.95/1.24    spl18_1 | ~spl18_2 | ~spl18_4 | spl18_16),
% 6.95/1.24    inference(avatar_contradiction_clause,[],[f598])).
% 6.95/1.24  fof(f598,plain,(
% 6.95/1.24    $false | (spl18_1 | ~spl18_2 | ~spl18_4 | spl18_16)),
% 6.95/1.24    inference(subsumption_resolution,[],[f597,f215])).
% 6.95/1.24  fof(f597,plain,(
% 6.95/1.24    ~l3_lattices(sK0) | (spl18_1 | ~spl18_2 | spl18_16)),
% 6.95/1.24    inference(subsumption_resolution,[],[f596,f200])).
% 6.95/1.24  fof(f596,plain,(
% 6.95/1.24    v2_struct_0(sK0) | ~l3_lattices(sK0) | (~spl18_2 | spl18_16)),
% 6.95/1.24    inference(subsumption_resolution,[],[f594,f205])).
% 6.95/1.24  fof(f594,plain,(
% 6.95/1.24    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl18_16),
% 6.95/1.24    inference(resolution,[],[f360,f124])).
% 6.95/1.24  fof(f124,plain,(
% 6.95/1.24    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f26])).
% 6.95/1.24  fof(f360,plain,(
% 6.95/1.24    ~v9_lattices(sK0) | spl18_16),
% 6.95/1.24    inference(avatar_component_clause,[],[f359])).
% 6.95/1.24  fof(f359,plain,(
% 6.95/1.24    spl18_16 <=> v9_lattices(sK0)),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).
% 6.95/1.24  fof(f591,plain,(
% 6.95/1.24    spl18_37 | spl18_1 | ~spl18_4 | ~spl18_16),
% 6.95/1.24    inference(avatar_split_clause,[],[f403,f359,f213,f198,f589])).
% 6.95/1.24  fof(f403,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1) ) | (spl18_1 | ~spl18_4 | ~spl18_16)),
% 6.95/1.24    inference(subsumption_resolution,[],[f402,f200])).
% 6.95/1.24  fof(f402,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_16)),
% 6.95/1.24    inference(subsumption_resolution,[],[f401,f361])).
% 6.95/1.24  fof(f361,plain,(
% 6.95/1.24    v9_lattices(sK0) | ~spl18_16),
% 6.95/1.24    inference(avatar_component_clause,[],[f359])).
% 6.95/1.24  fof(f401,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | k2_lattices(sK0,X1,k1_lattices(sK0,X1,X0)) = X1 | v2_struct_0(sK0)) ) | ~spl18_4),
% 6.95/1.24    inference(resolution,[],[f151,f215])).
% 6.95/1.24  fof(f151,plain,(
% 6.95/1.24    ( ! [X4,X0,X3] : (~l3_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f85])).
% 6.95/1.24  fof(f85,plain,(
% 6.95/1.24    ! [X0] : (((v9_lattices(X0) | ((sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f82,f84,f83])).
% 6.95/1.24  fof(f83,plain,(
% 6.95/1.24    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f84,plain,(
% 6.95/1.24    ! [X0] : (? [X2] : (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f82,plain,(
% 6.95/1.24    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f81])).
% 6.95/1.24  fof(f81,plain,(
% 6.95/1.24    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f44])).
% 6.95/1.24  fof(f44,plain,(
% 6.95/1.24    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f43])).
% 6.95/1.24  fof(f43,plain,(
% 6.95/1.24    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f6])).
% 6.95/1.24  fof(f6,axiom,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 6.95/1.24  fof(f494,plain,(
% 6.95/1.24    spl18_30 | spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f440,f213,f208,f203,f198,f492])).
% 6.95/1.24  fof(f440,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f439,f200])).
% 6.95/1.24  fof(f439,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f438,f205])).
% 6.95/1.24  fof(f438,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f437,f215])).
% 6.95/1.24  fof(f437,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_3),
% 6.95/1.24    inference(resolution,[],[f436,f210])).
% 6.95/1.24  fof(f436,plain,(
% 6.95/1.24    ( ! [X4,X0,X1] : (~v4_lattice3(X0) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(subsumption_resolution,[],[f193,f170])).
% 6.95/1.24  fof(f193,plain,(
% 6.95/1.24    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(duplicate_literal_removal,[],[f186])).
% 6.95/1.24  fof(f186,plain,(
% 6.95/1.24    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(equality_resolution,[],[f147])).
% 6.95/1.24  fof(f147,plain,(
% 6.95/1.24    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f80])).
% 6.95/1.24  fof(f486,plain,(
% 6.95/1.24    spl18_28 | ~spl18_8),
% 6.95/1.24    inference(avatar_split_clause,[],[f468,f242,f484])).
% 6.95/1.24  fof(f242,plain,(
% 6.95/1.24    spl18_8 <=> ! [X1,X0] : (r2_hidden(sK14(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).
% 6.95/1.24  fof(f468,plain,(
% 6.95/1.24    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | r4_lattice3(sK0,X16,k1_xboole_0)) ) | ~spl18_8),
% 6.95/1.24    inference(resolution,[],[f243,f217])).
% 6.95/1.24  fof(f217,plain,(
% 6.95/1.24    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 6.95/1.24    inference(superposition,[],[f169,f188])).
% 6.95/1.24  fof(f188,plain,(
% 6.95/1.24    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.95/1.24    inference(equality_resolution,[],[f173])).
% 6.95/1.24  fof(f173,plain,(
% 6.95/1.24    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.95/1.24    inference(cnf_transformation,[],[f101])).
% 6.95/1.24  fof(f101,plain,(
% 6.95/1.24    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.95/1.24    inference(flattening,[],[f100])).
% 6.95/1.24  fof(f100,plain,(
% 6.95/1.24    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.95/1.24    inference(nnf_transformation,[],[f1])).
% 6.95/1.24  fof(f1,axiom,(
% 6.95/1.24    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.95/1.24  fof(f169,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 6.95/1.24    inference(cnf_transformation,[],[f2])).
% 6.95/1.24  fof(f2,axiom,(
% 6.95/1.24    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 6.95/1.24  fof(f243,plain,(
% 6.95/1.24    ( ! [X0,X1] : (r2_hidden(sK14(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | ~spl18_8),
% 6.95/1.24    inference(avatar_component_clause,[],[f242])).
% 6.95/1.24  fof(f482,plain,(
% 6.95/1.24    spl18_27 | spl18_1 | ~spl18_3 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f347,f213,f208,f198,f480])).
% 6.95/1.24  fof(f347,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK12(sK0,X1),X0)) ) | (spl18_1 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f346,f200])).
% 6.95/1.24  fof(f346,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK12(sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f345,f215])).
% 6.95/1.24  fof(f345,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK12(sK0,X1),X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_3),
% 6.95/1.24    inference(resolution,[],[f157,f210])).
% 6.95/1.24  fof(f157,plain,(
% 6.95/1.24    ( ! [X6,X4,X0] : (~v4_lattice3(X0) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | r1_lattices(X0,sK12(X0,X4),X6) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f91])).
% 6.95/1.24  fof(f429,plain,(
% 6.95/1.24    spl18_24 | spl18_1 | ~spl18_4 | ~spl18_20),
% 6.95/1.24    inference(avatar_split_clause,[],[f425,f387,f213,f198,f427])).
% 6.95/1.24  fof(f387,plain,(
% 6.95/1.24    spl18_20 <=> ! [X2] : sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).
% 6.95/1.24  fof(f425,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0))) ) | (spl18_1 | ~spl18_4 | ~spl18_20)),
% 6.95/1.24    inference(subsumption_resolution,[],[f424,f200])).
% 6.95/1.24  fof(f424,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl18_4 | ~spl18_20)),
% 6.95/1.24    inference(subsumption_resolution,[],[f423,f215])).
% 6.95/1.24  fof(f423,plain,(
% 6.95/1.24    ( ! [X3] : (m1_subset_1(sK12(sK0,X3),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_20),
% 6.95/1.24    inference(superposition,[],[f170,f388])).
% 6.95/1.24  fof(f388,plain,(
% 6.95/1.24    ( ! [X2] : (sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))) ) | ~spl18_20),
% 6.95/1.24    inference(avatar_component_clause,[],[f387])).
% 6.95/1.24  fof(f389,plain,(
% 6.95/1.24    spl18_20 | spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_9),
% 6.95/1.24    inference(avatar_split_clause,[],[f280,f250,f213,f208,f198,f387])).
% 6.95/1.24  fof(f280,plain,(
% 6.95/1.24    ( ! [X2] : (sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2)))) ) | (spl18_1 | ~spl18_3 | ~spl18_4 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f279,f200])).
% 6.95/1.24  fof(f279,plain,(
% 6.95/1.24    ( ! [X2] : (sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2))) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f278,f215])).
% 6.95/1.24  fof(f278,plain,(
% 6.95/1.24    ( ! [X2] : (sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f265,f210])).
% 6.95/1.24  fof(f265,plain,(
% 6.95/1.24    ( ! [X2] : (sK12(sK0,X2) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK12(sK0,X2))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_9),
% 6.95/1.24    inference(resolution,[],[f251,f155])).
% 6.95/1.24  fof(f342,plain,(
% 6.95/1.24    spl18_13 | spl18_1 | ~spl18_4 | ~spl18_12),
% 6.95/1.24    inference(avatar_split_clause,[],[f337,f324,f213,f198,f339])).
% 6.95/1.24  fof(f324,plain,(
% 6.95/1.24    spl18_12 <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 6.95/1.24    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).
% 6.95/1.24  fof(f337,plain,(
% 6.95/1.24    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl18_1 | ~spl18_4 | ~spl18_12)),
% 6.95/1.24    inference(subsumption_resolution,[],[f336,f200])).
% 6.95/1.24  fof(f336,plain,(
% 6.95/1.24    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl18_4 | ~spl18_12)),
% 6.95/1.24    inference(subsumption_resolution,[],[f335,f215])).
% 6.95/1.24  fof(f335,plain,(
% 6.95/1.24    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl18_12),
% 6.95/1.24    inference(superposition,[],[f170,f326])).
% 6.95/1.24  fof(f326,plain,(
% 6.95/1.24    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl18_12),
% 6.95/1.24    inference(avatar_component_clause,[],[f324])).
% 6.95/1.24  fof(f334,plain,(
% 6.95/1.24    ~spl18_4 | spl18_11),
% 6.95/1.24    inference(avatar_contradiction_clause,[],[f333])).
% 6.95/1.24  fof(f333,plain,(
% 6.95/1.24    $false | (~spl18_4 | spl18_11)),
% 6.95/1.24    inference(subsumption_resolution,[],[f331,f215])).
% 6.95/1.24  fof(f331,plain,(
% 6.95/1.24    ~l3_lattices(sK0) | spl18_11),
% 6.95/1.24    inference(resolution,[],[f322,f116])).
% 6.95/1.24  fof(f322,plain,(
% 6.95/1.24    ~l1_lattices(sK0) | spl18_11),
% 6.95/1.24    inference(avatar_component_clause,[],[f320])).
% 6.95/1.24  fof(f327,plain,(
% 6.95/1.24    ~spl18_11 | spl18_12 | spl18_1 | ~spl18_9),
% 6.95/1.24    inference(avatar_split_clause,[],[f267,f250,f198,f324,f320])).
% 6.95/1.24  fof(f267,plain,(
% 6.95/1.24    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | (spl18_1 | ~spl18_9)),
% 6.95/1.24    inference(subsumption_resolution,[],[f257,f200])).
% 6.95/1.24  fof(f257,plain,(
% 6.95/1.24    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl18_9),
% 6.95/1.24    inference(resolution,[],[f251,f127])).
% 6.95/1.24  fof(f252,plain,(
% 6.95/1.24    spl18_9 | spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f248,f213,f208,f203,f198,f250])).
% 6.95/1.24  fof(f248,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0) ) | (spl18_1 | ~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f247,f200])).
% 6.95/1.24  fof(f247,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl18_2 | ~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f246,f205])).
% 6.95/1.24  fof(f246,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl18_3 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f245,f215])).
% 6.95/1.24  fof(f245,plain,(
% 6.95/1.24    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl18_3),
% 6.95/1.24    inference(resolution,[],[f141,f210])).
% 6.95/1.24  fof(f141,plain,(
% 6.95/1.24    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f38])).
% 6.95/1.24  fof(f38,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f37])).
% 6.95/1.24  fof(f37,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f18])).
% 6.95/1.24  fof(f18,axiom,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 6.95/1.24  fof(f244,plain,(
% 6.95/1.24    spl18_8 | spl18_1 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f236,f213,f198,f242])).
% 6.95/1.24  fof(f236,plain,(
% 6.95/1.24    ( ! [X0,X1] : (r2_hidden(sK14(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | (spl18_1 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f235,f200])).
% 6.95/1.24  fof(f235,plain,(
% 6.95/1.24    ( ! [X0,X1] : (r2_hidden(sK14(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl18_4),
% 6.95/1.24    inference(resolution,[],[f167,f215])).
% 6.95/1.24  fof(f167,plain,(
% 6.95/1.24    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK14(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 6.95/1.24    inference(cnf_transformation,[],[f99])).
% 6.95/1.24  fof(f99,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f97,f98])).
% 6.95/1.24  fof(f98,plain,(
% 6.95/1.24    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK14(X0,X1,X2),X1) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X0))))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f97,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(rectify,[],[f96])).
% 6.95/1.24  fof(f96,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(nnf_transformation,[],[f50])).
% 6.95/1.24  fof(f50,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f49])).
% 6.95/1.24  fof(f49,plain,(
% 6.95/1.24    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f11])).
% 6.95/1.24  fof(f11,axiom,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 6.95/1.24  fof(f232,plain,(
% 6.95/1.24    ~spl18_5 | ~spl18_6 | spl18_1 | ~spl18_2 | ~spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f223,f213,f203,f198,f229,f225])).
% 6.95/1.24  fof(f223,plain,(
% 6.95/1.24    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | (spl18_1 | ~spl18_2 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f222,f200])).
% 6.95/1.24  fof(f222,plain,(
% 6.95/1.24    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0) | (~spl18_2 | ~spl18_4)),
% 6.95/1.24    inference(subsumption_resolution,[],[f221,f205])).
% 6.95/1.24  fof(f221,plain,(
% 6.95/1.24    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl18_4),
% 6.95/1.24    inference(subsumption_resolution,[],[f115,f215])).
% 6.95/1.24  fof(f115,plain,(
% 6.95/1.24    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 6.95/1.24    inference(cnf_transformation,[],[f58])).
% 6.95/1.24  fof(f58,plain,(
% 6.95/1.24    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 6.95/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f57])).
% 6.95/1.24  fof(f57,plain,(
% 6.95/1.24    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 6.95/1.24    introduced(choice_axiom,[])).
% 6.95/1.24  fof(f23,plain,(
% 6.95/1.24    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 6.95/1.24    inference(flattening,[],[f22])).
% 6.95/1.24  fof(f22,plain,(
% 6.95/1.24    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 6.95/1.24    inference(ennf_transformation,[],[f21])).
% 6.95/1.24  fof(f21,negated_conjecture,(
% 6.95/1.24    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 6.95/1.24    inference(negated_conjecture,[],[f20])).
% 6.95/1.24  fof(f20,conjecture,(
% 6.95/1.24    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 6.95/1.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 6.95/1.24  fof(f216,plain,(
% 6.95/1.24    spl18_4),
% 6.95/1.24    inference(avatar_split_clause,[],[f114,f213])).
% 6.95/1.24  fof(f114,plain,(
% 6.95/1.24    l3_lattices(sK0)),
% 6.95/1.24    inference(cnf_transformation,[],[f58])).
% 6.95/1.24  fof(f211,plain,(
% 6.95/1.24    spl18_3),
% 6.95/1.24    inference(avatar_split_clause,[],[f113,f208])).
% 6.95/1.24  fof(f113,plain,(
% 6.95/1.24    v4_lattice3(sK0)),
% 6.95/1.24    inference(cnf_transformation,[],[f58])).
% 6.95/1.24  fof(f206,plain,(
% 6.95/1.24    spl18_2),
% 6.95/1.24    inference(avatar_split_clause,[],[f112,f203])).
% 6.95/1.24  fof(f112,plain,(
% 6.95/1.24    v10_lattices(sK0)),
% 6.95/1.24    inference(cnf_transformation,[],[f58])).
% 6.95/1.24  fof(f201,plain,(
% 6.95/1.24    ~spl18_1),
% 6.95/1.24    inference(avatar_split_clause,[],[f111,f198])).
% 6.95/1.24  fof(f111,plain,(
% 6.95/1.24    ~v2_struct_0(sK0)),
% 6.95/1.24    inference(cnf_transformation,[],[f58])).
% 6.95/1.24  % SZS output end Proof for theBenchmark
% 6.95/1.24  % (25285)------------------------------
% 6.95/1.24  % (25285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.24  % (25285)Termination reason: Refutation
% 6.95/1.24  
% 6.95/1.24  % (25285)Memory used [KB]: 14711
% 6.95/1.24  % (25285)Time elapsed: 0.802 s
% 6.95/1.24  % (25285)------------------------------
% 6.95/1.24  % (25285)------------------------------
% 7.18/1.26  % (25281)Success in time 0.896 s
%------------------------------------------------------------------------------
