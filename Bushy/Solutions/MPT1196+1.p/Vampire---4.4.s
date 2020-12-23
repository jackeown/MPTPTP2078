%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t22_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  258 (1501 expanded)
%              Number of leaves         :   59 ( 665 expanded)
%              Depth                    :   23
%              Number of atoms          : 1291 (6556 expanded)
%              Number of equality atoms :   93 ( 639 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f130,f137,f144,f151,f158,f165,f172,f179,f186,f195,f202,f212,f219,f226,f233,f264,f271,f278,f297,f313,f320,f327,f334,f371,f378,f411,f418,f425,f432,f444,f451,f543,f552,f559,f566,f573,f580,f589,f596,f6786,f6970,f7047])).

fof(f7047,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | spl9_31
    | ~ spl9_44
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f7046])).

fof(f7046,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_44
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f7045,f433])).

fof(f433,plain,
    ( k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f232,f326,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',d3_lattices)).

fof(f326,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl9_44
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f232,plain,
    ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl9_31
  <=> ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f178,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl9_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f194,plain,
    ( l2_lattices(sK0)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl9_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f7045,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f816,f370])).

fof(f370,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl9_48
  <=> k1_lattices(sK0,sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f816,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f178,f185,f97])).

fof(f97,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v5_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),sK5(X0)) != k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f70,f73,f72,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k1_lattices(X0,sK3(X0),X2),X3) != k1_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,X1,k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k1_lattices(X0,X1,sK4(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,k1_lattices(X0,X2,sK5(X0))) != k1_lattices(X0,k1_lattices(X0,X1,X2),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',d5_lattices)).

fof(f185,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f129,plain,
    ( v5_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_2
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f6970,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | spl9_31
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_66 ),
    inference(avatar_contradiction_clause,[],[f6969])).

fof(f6969,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f6968,f433])).

fof(f6968,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f6420,f4726])).

fof(f4726,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1260,f393])).

fof(f393,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f136,f143,f150,f157,f326,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k1_lattices(X0,X1,X1) = X1
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',t17_lattices)).

fof(f157,plain,
    ( l3_lattices(sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_10
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f150,plain,
    ( v9_lattices(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl9_8
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f143,plain,
    ( v8_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_6
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f136,plain,
    ( v6_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl9_4
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1260,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f185,f326,f97])).

fof(f6420,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_66 ),
    inference(backward_demodulation,[],[f817,f5138])).

fof(f5138,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f1104,f370])).

fof(f1104,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_66 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f178,f551,f97])).

fof(f551,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),u1_struct_0(sK0))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl9_66
  <=> m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f817,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f178,f185,f97])).

fof(f6786,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | spl9_31
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(avatar_contradiction_clause,[],[f6785])).

fof(f6785,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_31
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f6784,f433])).

fof(f6784,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f6593,f4726])).

fof(f6593,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f6554,f4808])).

fof(f4808,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)))) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f1249,f4629])).

fof(f4629,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4628,f1332])).

fof(f1332,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f319,f326,f97])).

fof(f319,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl9_42
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f4628,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_48
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4627,f3500])).

fof(f3500,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1680,f370])).

fof(f1680,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f178,f319,f97])).

fof(f4627,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f1320,f1332])).

fof(f1320,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_44
    | ~ spl9_68 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f178,f558,f326,f97])).

fof(f558,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl9_68
  <=> m1_subset_1(k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f1249,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f178,f326,f97])).

fof(f6554,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f6548,f6248])).

fof(f6248,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f6227,f4809])).

fof(f4809,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(backward_demodulation,[],[f1249,f4672])).

fof(f4672,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2)),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1303,f393])).

fof(f1303,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f326,f326,f97])).

fof(f6227,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64 ),
    inference(backward_demodulation,[],[f6221,f1262])).

fof(f1262,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44
    | ~ spl9_64 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f542,f185,f326,f97])).

fof(f542,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),u1_struct_0(sK0))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl9_64
  <=> m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f6221,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f823,f1249])).

fof(f823,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f178,f185,f97])).

fof(f6548,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f6540,f5859])).

fof(f5859,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5845,f1267])).

fof(f1267,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f185,f326,f97])).

fof(f5845,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f5833,f5091])).

fof(f5091,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2))),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66 ),
    inference(backward_demodulation,[],[f1111,f4707])).

fof(f4707,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66 ),
    inference(backward_demodulation,[],[f1267,f1286])).

fof(f1286,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_44
    | ~ spl9_64
    | ~ spl9_66 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f542,f551,f326,f97])).

fof(f1111,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_66 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f178,f551,f97])).

fof(f5833,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f5798,f1111])).

fof(f5798,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f5780,f5110])).

fof(f5110,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2))) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f1105,f4901])).

fof(f4901,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_64
    | ~ spl9_66
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f1190,f3628])).

fof(f3628,plain,
    ( k1_lattices(sK0,sK2,sK1) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f3624,f1687])).

fof(f1687,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f178,f319,f97])).

fof(f3624,plain,
    ( k1_lattices(sK0,sK2,sK1) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f3623,f3489])).

fof(f3489,plain,
    ( k1_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f1681,f383])).

fof(f383,plain,
    ( k1_lattices(sK0,sK2,sK1) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f136,f143,f150,f157,f319,f96])).

fof(f1681,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f178,f319,f97])).

fof(f3623,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f1609,f646])).

fof(f646,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_68 ),
    inference(unit_resulting_resolution,[],[f122,f136,f143,f150,f157,f558,f96])).

fof(f1609,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))) = k1_lattices(sK0,sK2,k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_68 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f558,f558,f97])).

fof(f1190,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_64
    | ~ spl9_66 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f542,f319,f551,f97])).

fof(f1105,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_66 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f178,f551,f97])).

fof(f5780,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5779,f383])).

fof(f5779,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK1)),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f907,f1105])).

fof(f907,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK1)),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f319,f319,f185,f97])).

fof(f6540,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f6278,f4679])).

fof(f4679,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)),k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1297,f393])).

fof(f1297,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f129,f185,f326,f326,f97])).

fof(f6278,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42
    | ~ spl9_44 ),
    inference(backward_demodulation,[],[f817,f1267])).

fof(f596,plain,
    ( spl9_78
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f400,f325,f193,f184,f121,f594])).

fof(f594,plain,
    ( spl9_78
  <=> m1_subset_1(k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f400,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f326,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',dt_k1_lattices)).

fof(f589,plain,
    ( spl9_76
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f399,f325,f193,f177,f121,f587])).

fof(f587,plain,
    ( spl9_76
  <=> m1_subset_1(k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f399,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f326,f110])).

fof(f580,plain,
    ( spl9_74
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f395,f325,f193,f184,f121,f578])).

fof(f578,plain,
    ( spl9_74
  <=> m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f395,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f326,f110])).

fof(f573,plain,
    ( spl9_72
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f394,f325,f193,f177,f121,f571])).

fof(f571,plain,
    ( spl9_72
  <=> m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f394,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f326,f110])).

fof(f566,plain,
    ( spl9_70
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f389,f318,f193,f184,f121,f564])).

fof(f564,plain,
    ( spl9_70
  <=> m1_subset_1(k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f389,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f319,f110])).

fof(f559,plain,
    ( spl9_68
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f388,f318,f193,f177,f121,f557])).

fof(f388,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f319,f110])).

fof(f552,plain,
    ( spl9_66
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f385,f318,f193,f184,f121,f550])).

fof(f385,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f319,f110])).

fof(f543,plain,
    ( spl9_64
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f384,f318,f193,f177,f121,f541])).

fof(f384,plain,
    ( m1_subset_1(k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f319,f110])).

fof(f451,plain,
    ( spl9_62
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f435,f376,f193,f184,f121,f449])).

fof(f449,plain,
    ( spl9_62
  <=> r1_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f376,plain,
    ( spl9_50
  <=> k1_lattices(sK0,sK2,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f435,plain,
    ( r1_lattices(sK0,sK2,sK2)
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_50 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f185,f377,f103])).

fof(f377,plain,
    ( k1_lattices(sK0,sK2,sK2) = sK2
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f376])).

fof(f444,plain,
    ( spl9_60
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f434,f369,f193,f177,f121,f442])).

fof(f442,plain,
    ( spl9_60
  <=> r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f434,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20
    | ~ spl9_48 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f178,f370,f103])).

fof(f432,plain,
    ( spl9_58
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f305,f193,f184,f121,f430])).

fof(f430,plain,
    ( spl9_58
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK6(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f305,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK6(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f104,f110])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',existence_m1_subset_1)).

fof(f425,plain,
    ( spl9_56
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f304,f193,f177,f121,f423])).

fof(f423,plain,
    ( spl9_56
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK6(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f304,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK6(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f104,f110])).

fof(f418,plain,
    ( spl9_54
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f303,f193,f184,f121,f416])).

fof(f416,plain,
    ( spl9_54
  <=> m1_subset_1(k1_lattices(sK0,sK6(u1_struct_0(sK0)),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f303,plain,
    ( m1_subset_1(k1_lattices(sK0,sK6(u1_struct_0(sK0)),sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f104,f185,f110])).

fof(f411,plain,
    ( spl9_52
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f300,f193,f177,f121,f409])).

fof(f409,plain,
    ( spl9_52
  <=> m1_subset_1(k1_lattices(sK0,sK6(u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f300,plain,
    ( m1_subset_1(k1_lattices(sK0,sK6(u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f104,f178,f110])).

fof(f378,plain,
    ( spl9_50
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f344,f184,f156,f149,f142,f135,f121,f376])).

fof(f344,plain,
    ( k1_lattices(sK0,sK2,sK2) = sK2
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f122,f136,f143,f150,f157,f185,f96])).

fof(f371,plain,
    ( spl9_48
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f343,f177,f156,f149,f142,f135,f121,f369])).

fof(f343,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f122,f136,f143,f150,f157,f178,f96])).

fof(f334,plain,
    ( spl9_46
    | spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f302,f193,f184,f121,f332])).

fof(f332,plain,
    ( spl9_46
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f302,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f185,f110])).

fof(f327,plain,
    ( spl9_44
    | spl9_1
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f301,f193,f184,f177,f121,f325])).

fof(f301,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f185,f110])).

fof(f320,plain,
    ( spl9_42
    | spl9_1
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f299,f193,f184,f177,f121,f318])).

fof(f299,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f185,f178,f110])).

fof(f313,plain,
    ( spl9_40
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f298,f193,f177,f121,f311])).

fof(f311,plain,
    ( spl9_40
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f298,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f122,f194,f178,f178,f110])).

fof(f297,plain,
    ( spl9_38
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f279,f170,f295])).

fof(f295,plain,
    ( spl9_38
  <=> m1_subset_1(u2_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f170,plain,
    ( spl9_14
  <=> l2_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f279,plain,
    ( m1_subset_1(u2_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))))
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f171,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',dt_u2_lattices)).

fof(f171,plain,
    ( l2_lattices(sK8)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f278,plain,
    ( spl9_36
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f257,f200,f276])).

fof(f276,plain,
    ( spl9_36
  <=> v1_funct_2(u2_lattices(sK7),k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f200,plain,
    ( spl9_22
  <=> l2_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f257,plain,
    ( v1_funct_2(u2_lattices(sK7),k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f201,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f201,plain,
    ( l2_lattices(sK7)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f271,plain,
    ( spl9_34
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f256,f193,f269])).

fof(f269,plain,
    ( spl9_34
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f256,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f194,f94])).

fof(f264,plain,
    ( spl9_32
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f255,f170,f262])).

fof(f262,plain,
    ( spl9_32
  <=> v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f255,plain,
    ( v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f171,f94])).

fof(f233,plain,(
    ~ spl9_31 ),
    inference(avatar_split_clause,[],[f90,f231])).

fof(f90,plain,(
    ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & v5_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f67,f66,f65])).

fof(f65,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & v5_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_lattices(X0,sK1,k1_lattices(X0,sK1,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',t22_lattices)).

fof(f226,plain,
    ( spl9_28
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f205,f200,f224])).

fof(f224,plain,
    ( spl9_28
  <=> v1_funct_1(u2_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f205,plain,
    ( v1_funct_1(u2_lattices(sK7))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f201,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f219,plain,
    ( spl9_26
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f204,f193,f217])).

fof(f217,plain,
    ( spl9_26
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f204,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f194,f93])).

fof(f212,plain,
    ( spl9_24
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f203,f170,f210])).

fof(f210,plain,
    ( spl9_24
  <=> v1_funct_1(u2_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f203,plain,
    ( v1_funct_1(u2_lattices(sK8))
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f171,f93])).

fof(f202,plain,
    ( spl9_22
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f188,f163,f200])).

fof(f163,plain,
    ( spl9_12
  <=> l3_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f188,plain,
    ( l2_lattices(sK7)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f164,f92])).

fof(f92,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',dt_l3_lattices)).

fof(f164,plain,
    ( l3_lattices(sK7)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f195,plain,
    ( spl9_20
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f187,f156,f193])).

fof(f187,plain,
    ( l2_lattices(sK0)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f157,f92])).

fof(f186,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f89,f184])).

fof(f89,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f179,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f88,f177])).

fof(f88,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f172,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f116,f170])).

fof(f116,plain,(
    l2_lattices(sK8) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    l2_lattices(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f80])).

fof(f80,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK8) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',existence_l2_lattices)).

fof(f165,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f115,f163])).

fof(f115,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    l3_lattices(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f78])).

fof(f78,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK7) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',existence_l3_lattices)).

fof(f158,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f87,f156])).

fof(f87,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f151,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f86,f149])).

fof(f86,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f144,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f85,f142])).

fof(f85,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f137,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f84,f135])).

fof(f84,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f83,f128])).

fof(f83,plain,(
    v5_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f123,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f82,f121])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
