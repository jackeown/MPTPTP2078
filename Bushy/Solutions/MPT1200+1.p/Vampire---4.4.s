%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t27_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:01 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  311 (1049 expanded)
%              Number of leaves         :   92 ( 503 expanded)
%              Depth                    :   12
%              Number of atoms          : 1108 (3942 expanded)
%              Number of equality atoms :   70 ( 196 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18023,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f164,f171,f178,f185,f192,f199,f206,f213,f220,f227,f238,f245,f252,f259,f272,f279,f286,f293,f300,f307,f317,f345,f352,f359,f369,f376,f387,f406,f413,f422,f432,f440,f447,f470,f477,f484,f491,f498,f521,f528,f535,f542,f573,f704,f711,f718,f725,f821,f828,f835,f842,f978,f1986,f1993,f2004,f2011,f2018,f2025,f2032,f2045,f2054,f10288])).

fof(f10288,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | spl13_45
    | ~ spl13_82
    | ~ spl13_84
    | ~ spl13_106 ),
    inference(avatar_contradiction_clause,[],[f10287])).

fof(f10287,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_45
    | ~ spl13_82
    | ~ spl13_84
    | ~ spl13_106 ),
    inference(subsumption_resolution,[],[f10284,f1063])).

fof(f1063,plain,
    ( k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_26
    | ~ spl13_45
    | ~ spl13_82
    | ~ spl13_84 ),
    inference(unit_resulting_resolution,[],[f149,f244,f527,f316,f534,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',d3_lattices)).

fof(f534,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_84 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl13_84
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f316,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl13_45
  <=> ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f527,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl13_82
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f244,plain,
    ( l2_lattices(sK0)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl13_26
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f149,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f10284,plain,
    ( k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_84
    | ~ spl13_106 ),
    inference(backward_demodulation,[],[f10282,f1059])).

fof(f1059,plain,
    ( k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_84 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f205,f534,f118])).

fof(f118,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK5(X0)) != sK5(X0)
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f78,f80,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK4(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK5(X0)),sK5(X0)) != sK5(X0)
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',d8_lattices)).

fof(f205,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl13_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f163,plain,
    ( v8_lattices(sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl13_4
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f177,plain,
    ( l3_lattices(sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl13_8
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f10282,plain,
    ( k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_106 ),
    inference(forward_demodulation,[],[f9617,f977])).

fof(f977,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1
    | ~ spl13_106 ),
    inference(avatar_component_clause,[],[f976])).

fof(f976,plain,
    ( spl13_106
  <=> k2_lattices(sK0,sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f9617,plain,
    ( k2_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f156,f205,f212,f219,f122])).

fof(f122,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v7_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ( k2_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK8(X0)) != k2_lattices(X0,sK6(X0),k2_lattices(X0,sK7(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f83,f86,f85,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,k2_lattices(X0,sK6(X0),X2),X3) != k2_lattices(X0,sK6(X0),k2_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,X1,k2_lattices(X0,sK7(X0),X3)) != k2_lattices(X0,k2_lattices(X0,X1,sK7(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k2_lattices(X0,X2,sK8(X0))) != k2_lattices(X0,k2_lattices(X0,X1,X2),sK8(X0))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',d7_lattices)).

fof(f219,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl13_20
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f212,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl13_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f156,plain,
    ( v7_lattices(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl13_2
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f237,plain,
    ( l1_lattices(sK0)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl13_24
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f2054,plain,
    ( spl13_124
    | spl13_1
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f2046,f1984,f468,f243,f204,f148,f2052])).

fof(f2052,plain,
    ( spl13_124
  <=> r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f468,plain,
    ( spl13_70
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f1984,plain,
    ( spl13_108
  <=> k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f2046,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_108 ),
    inference(unit_resulting_resolution,[],[f149,f244,f205,f469,f1985,f128])).

fof(f1985,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl13_108 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f469,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f468])).

fof(f2045,plain,
    ( spl13_122
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f796,f218,f176,f162,f148,f2043])).

fof(f2043,plain,
    ( spl13_122
  <=> k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f796,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f219,f219,f118])).

fof(f2032,plain,
    ( spl13_120
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f795,f218,f211,f176,f162,f148,f2030])).

fof(f2030,plain,
    ( spl13_120
  <=> k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f795,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f212,f219,f118])).

fof(f2025,plain,
    ( spl13_118
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f794,f218,f204,f176,f162,f148,f2023])).

fof(f2023,plain,
    ( spl13_118
  <=> k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f794,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f205,f219,f118])).

fof(f2018,plain,
    ( spl13_116
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f787,f218,f211,f176,f162,f148,f2016])).

fof(f2016,plain,
    ( spl13_116
  <=> k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f787,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f219,f212,f118])).

fof(f2011,plain,
    ( spl13_114
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f786,f211,f176,f162,f148,f2009])).

fof(f2009,plain,
    ( spl13_114
  <=> k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f786,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f212,f212,f118])).

fof(f2004,plain,
    ( spl13_112
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f778,f218,f204,f176,f162,f148,f2002])).

fof(f2002,plain,
    ( spl13_112
  <=> k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f778,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f219,f205,f118])).

fof(f1993,plain,
    ( spl13_110
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f777,f211,f204,f176,f162,f148,f1991])).

fof(f1991,plain,
    ( spl13_110
  <=> k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f777,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f212,f205,f118])).

fof(f1986,plain,
    ( spl13_108
    | spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f776,f204,f176,f162,f148,f1984])).

fof(f776,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_8
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f149,f177,f163,f205,f205,f118])).

fof(f978,plain,
    ( spl13_106
    | spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f904,f225,f211,f204,f176,f169,f162,f148,f976])).

fof(f169,plain,
    ( spl13_6
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f225,plain,
    ( spl13_22
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f904,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f149,f163,f170,f177,f205,f226,f212,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',t21_lattices)).

fof(f226,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f170,plain,
    ( v9_lattices(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f842,plain,
    ( spl13_104
    | spl13_1
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f509,f243,f218,f148,f840])).

fof(f840,plain,
    ( spl13_104
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f509,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f219,f219,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',dt_k1_lattices)).

fof(f835,plain,
    ( spl13_102
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f508,f243,f218,f211,f148,f833])).

fof(f833,plain,
    ( spl13_102
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f508,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f212,f219,f136])).

fof(f828,plain,
    ( spl13_100
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f507,f243,f218,f204,f148,f826])).

fof(f826,plain,
    ( spl13_100
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f507,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f205,f219,f136])).

fof(f821,plain,
    ( spl13_98
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f505,f243,f218,f211,f148,f819])).

fof(f819,plain,
    ( spl13_98
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f505,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f219,f212,f136])).

fof(f725,plain,
    ( spl13_96
    | spl13_1
    | ~ spl13_18
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f504,f243,f211,f148,f723])).

fof(f723,plain,
    ( spl13_96
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f504,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f212,f212,f136])).

fof(f718,plain,
    ( spl13_94
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f501,f243,f218,f204,f148,f716])).

fof(f716,plain,
    ( spl13_94
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f501,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f219,f205,f136])).

fof(f711,plain,
    ( spl13_92
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f500,f243,f211,f204,f148,f709])).

fof(f709,plain,
    ( spl13_92
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f500,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f212,f205,f136])).

fof(f704,plain,
    ( spl13_90
    | spl13_1
    | ~ spl13_16
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f499,f243,f204,f148,f702])).

fof(f702,plain,
    ( spl13_90
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f499,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f205,f205,f136])).

fof(f573,plain,
    ( spl13_88
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f563,f243,f225,f211,f204,f148,f571])).

fof(f571,plain,
    ( spl13_88
  <=> k1_lattices(sK0,sK1,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f563,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f149,f244,f205,f226,f212,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k1_lattices(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f88])).

fof(f542,plain,
    ( spl13_86
    | spl13_1
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f458,f236,f218,f148,f540])).

fof(f540,plain,
    ( spl13_86
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f458,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f219,f219,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',dt_k2_lattices)).

fof(f535,plain,
    ( spl13_84
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f457,f236,f218,f211,f148,f533])).

fof(f457,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f212,f219,f135])).

fof(f528,plain,
    ( spl13_82
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f456,f236,f218,f204,f148,f526])).

fof(f456,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f205,f219,f135])).

fof(f521,plain,
    ( spl13_80
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f454,f236,f218,f211,f148,f519])).

fof(f519,plain,
    ( spl13_80
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f454,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f219,f212,f135])).

fof(f498,plain,
    ( spl13_78
    | spl13_1
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f453,f236,f211,f148,f496])).

fof(f496,plain,
    ( spl13_78
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f453,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f212,f212,f135])).

fof(f491,plain,
    ( spl13_76
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f452,f236,f211,f204,f148,f489])).

fof(f489,plain,
    ( spl13_76
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f452,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f205,f212,f135])).

fof(f484,plain,
    ( spl13_74
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f450,f236,f218,f204,f148,f482])).

fof(f482,plain,
    ( spl13_74
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f450,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f219,f205,f135])).

fof(f477,plain,
    ( spl13_72
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f449,f236,f211,f204,f148,f475])).

fof(f475,plain,
    ( spl13_72
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f449,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f212,f205,f135])).

fof(f470,plain,
    ( spl13_70
    | spl13_1
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f448,f236,f204,f148,f468])).

fof(f448,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f149,f237,f205,f205,f135])).

fof(f447,plain,
    ( spl13_68
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f397,f236,f445])).

fof(f445,plain,
    ( spl13_68
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f397,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f237,f115])).

fof(f115,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',dt_u1_lattices)).

fof(f440,plain,
    ( spl13_66
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f378,f243,f438])).

fof(f438,plain,
    ( spl13_66
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f378,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f244,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',dt_u2_lattices)).

fof(f432,plain,
    ( ~ spl13_65
    | ~ spl13_60 ),
    inference(avatar_split_clause,[],[f424,f411,f430])).

fof(f430,plain,
    ( spl13_65
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)),u1_lattices(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f411,plain,
    ( spl13_60
  <=> m1_subset_1(u1_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f424,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)),u1_lattices(sK12))
    | ~ spl13_60 ),
    inference(unit_resulting_resolution,[],[f412,f325])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f324,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',t5_subset)).

fof(f324,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f323,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',t4_subset)).

fof(f323,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f309,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',t2_subset)).

fof(f309,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f132,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',antisymmetry_r2_hidden)).

fof(f412,plain,
    ( m1_subset_1(u1_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))))
    | ~ spl13_60 ),
    inference(avatar_component_clause,[],[f411])).

fof(f422,plain,
    ( ~ spl13_63
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f414,f404,f420])).

fof(f420,plain,
    ( spl13_63
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)),u2_lattices(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f404,plain,
    ( spl13_58
  <=> m1_subset_1(u2_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f414,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)),u2_lattices(sK11))
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f405,f325])).

fof(f405,plain,
    ( m1_subset_1(u2_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))))
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f404])).

fof(f413,plain,
    ( spl13_60
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f396,f197,f411])).

fof(f197,plain,
    ( spl13_14
  <=> l1_lattices(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f396,plain,
    ( m1_subset_1(u1_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))))
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f198,f115])).

fof(f198,plain,
    ( l1_lattices(sK12)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f406,plain,
    ( spl13_58
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f377,f190,f404])).

fof(f190,plain,
    ( spl13_12
  <=> l2_lattices(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f377,plain,
    ( m1_subset_1(u2_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f191,f112])).

fof(f191,plain,
    ( l2_lattices(sK11)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f387,plain,
    ( spl13_56
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f362,f250,f385])).

fof(f385,plain,
    ( spl13_56
  <=> v1_funct_2(u1_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f250,plain,
    ( spl13_28
  <=> l1_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f362,plain,
    ( v1_funct_2(u1_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f251,f114])).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f251,plain,
    ( l1_lattices(sK10)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f376,plain,
    ( spl13_54
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f361,f236,f374])).

fof(f374,plain,
    ( spl13_54
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f361,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f237,f114])).

fof(f369,plain,
    ( spl13_52
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f360,f197,f367])).

fof(f367,plain,
    ( spl13_52
  <=> v1_funct_2(u1_lattices(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f360,plain,
    ( v1_funct_2(u1_lattices(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f198,f114])).

fof(f359,plain,
    ( spl13_50
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f338,f257,f357])).

fof(f357,plain,
    ( spl13_50
  <=> v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f257,plain,
    ( spl13_30
  <=> l2_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f338,plain,
    ( v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f258,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f258,plain,
    ( l2_lattices(sK10)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f257])).

fof(f352,plain,
    ( spl13_48
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f337,f243,f350])).

fof(f350,plain,
    ( spl13_48
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f337,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f244,f111])).

fof(f345,plain,
    ( spl13_46
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f336,f190,f343])).

fof(f343,plain,
    ( spl13_46
  <=> v1_funct_2(u2_lattices(sK11),k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f336,plain,
    ( v1_funct_2(u2_lattices(sK11),k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f191,f111])).

fof(f317,plain,(
    ~ spl13_45 ),
    inference(avatar_split_clause,[],[f106,f315])).

fof(f106,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v7_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f74,f73,f72,f71])).

fof(f71,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3))
                  & r1_lattices(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v7_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(X0,k2_lattices(X0,sK1,X3),k2_lattices(X0,X2,X3))
                & r1_lattices(X0,sK1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,sK2,X3))
            & r1_lattices(X0,X1,sK2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k2_lattices(X0,X1,sK3),k2_lattices(X0,X2,sK3))
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',t27_lattices)).

fof(f307,plain,
    ( spl13_42
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f265,f250,f305])).

fof(f305,plain,
    ( spl13_42
  <=> v1_funct_1(u1_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f265,plain,
    ( v1_funct_1(u1_lattices(sK10))
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f251,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f300,plain,
    ( spl13_40
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f262,f257,f298])).

fof(f298,plain,
    ( spl13_40
  <=> v1_funct_1(u2_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f262,plain,
    ( v1_funct_1(u2_lattices(sK10))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f258,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f293,plain,
    ( spl13_38
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f264,f236,f291])).

fof(f291,plain,
    ( spl13_38
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f264,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f237,f113])).

fof(f286,plain,
    ( spl13_36
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f261,f243,f284])).

fof(f284,plain,
    ( spl13_36
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f261,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f244,f110])).

fof(f279,plain,
    ( spl13_34
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f263,f197,f277])).

fof(f277,plain,
    ( spl13_34
  <=> v1_funct_1(u1_lattices(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f263,plain,
    ( v1_funct_1(u1_lattices(sK12))
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f198,f113])).

fof(f272,plain,
    ( spl13_32
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f260,f190,f270])).

fof(f270,plain,
    ( spl13_32
  <=> v1_funct_1(u2_lattices(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f260,plain,
    ( v1_funct_1(u2_lattices(sK11))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f191,f110])).

fof(f259,plain,
    ( spl13_30
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f231,f183,f257])).

fof(f183,plain,
    ( spl13_10
  <=> l3_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f231,plain,
    ( l2_lattices(sK10)
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f184,f109])).

fof(f109,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',dt_l3_lattices)).

fof(f184,plain,
    ( l3_lattices(sK10)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f252,plain,
    ( spl13_28
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f229,f183,f250])).

fof(f229,plain,
    ( l1_lattices(sK10)
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f184,f108])).

fof(f108,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f245,plain,
    ( spl13_26
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f230,f176,f243])).

fof(f230,plain,
    ( l2_lattices(sK0)
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f177,f109])).

fof(f238,plain,
    ( spl13_24
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f228,f176,f236])).

fof(f228,plain,
    ( l1_lattices(sK0)
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f177,f108])).

fof(f227,plain,(
    spl13_22 ),
    inference(avatar_split_clause,[],[f105,f225])).

fof(f105,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f220,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f104,f218])).

fof(f104,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f213,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f103,f211])).

fof(f103,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f206,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f102,f204])).

fof(f102,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f199,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f143,f197])).

fof(f143,plain,(
    l1_lattices(sK12) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    l1_lattices(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f22,f95])).

fof(f95,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK12) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',existence_l1_lattices)).

fof(f192,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f142,f190])).

fof(f142,plain,(
    l2_lattices(sK11) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l2_lattices(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f24,f93])).

fof(f93,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK11) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',existence_l2_lattices)).

fof(f185,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f141,f183])).

fof(f141,plain,(
    l3_lattices(sK10) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    l3_lattices(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f25,f91])).

fof(f91,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK10) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t27_lattices.p',existence_l3_lattices)).

fof(f178,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f101,f176])).

fof(f101,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f171,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f100,f169])).

fof(f100,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f164,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f99,f162])).

fof(f99,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f157,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f98,f155])).

fof(f98,plain,(
    v7_lattices(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f150,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f97,f148])).

fof(f97,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------
