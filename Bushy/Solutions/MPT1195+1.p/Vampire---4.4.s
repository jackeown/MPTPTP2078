%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t21_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  270 ( 784 expanded)
%              Number of leaves         :   79 ( 345 expanded)
%              Depth                    :   12
%              Number of atoms          :  884 (2861 expanded)
%              Number of equality atoms :   75 ( 283 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f148,f155,f162,f169,f176,f183,f190,f197,f208,f215,f222,f229,f242,f249,f256,f263,f270,f277,f293,f296,f332,f342,f349,f356,f367,f374,f385,f392,f401,f411,f419,f426,f435,f456,f463,f470,f544,f551,f558,f565,f708,f716,f724,f731,f738,f852,f859,f866,f873,f981,f1006])).

fof(f1006,plain,
    ( spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_38
    | spl11_85 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_38
    | ~ spl11_85 ),
    inference(subsumption_resolution,[],[f286,f717])).

fof(f717,plain,
    ( ~ r1_lattices(sK0,sK1,sK2)
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_85 ),
    inference(unit_resulting_resolution,[],[f140,f214,f189,f196,f715,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d3_lattices)).

fof(f715,plain,
    ( k1_lattices(sK0,sK1,sK2) != sK2
    | ~ spl11_85 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl11_85
  <=> k1_lattices(sK0,sK1,sK2) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f196,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl11_16
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f189,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl11_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f214,plain,
    ( l2_lattices(sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl11_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f140,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f286,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl11_38
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f981,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_40
    | spl11_85 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_40
    | ~ spl11_85 ),
    inference(subsumption_resolution,[],[f979,f715])).

fof(f979,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_40 ),
    inference(forward_demodulation,[],[f962,f292])).

fof(f292,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl11_40
  <=> k2_lattices(sK0,sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f962,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f140,f161,f147,f189,f196,f114])).

fof(f114,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK5(X0),sK6(X0)),sK6(X0)) != sK6(X0)
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f80,f82,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK5(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK6(X0)),sK6(X0)) != sK6(X0)
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
    inference(rectify,[],[f79])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f48])).

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
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d8_lattices)).

fof(f147,plain,
    ( v8_lattices(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl11_2
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f161,plain,
    ( l3_lattices(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl11_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f873,plain,
    ( spl11_98
    | spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f827,f195,f160,f153,f139,f871])).

fof(f871,plain,
    ( spl11_98
  <=> k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f153,plain,
    ( spl11_4
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f827,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) = sK2
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f140,f161,f154,f196,f196,f110])).

fof(f110,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),sK4(X0))) != sK3(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f75,f77,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK3(X0),X2)) != sK3(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK4(X0))) != X1
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
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
    inference(rectify,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d9_lattices)).

fof(f154,plain,
    ( v9_lattices(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f866,plain,
    ( spl11_96
    | spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f826,f195,f188,f160,f153,f139,f864])).

fof(f864,plain,
    ( spl11_96
  <=> k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f826,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = sK1
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f140,f161,f154,f189,f196,f110])).

fof(f859,plain,
    ( spl11_94
    | spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f817,f195,f188,f160,f153,f139,f857])).

fof(f857,plain,
    ( spl11_94
  <=> k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f817,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = sK2
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f140,f161,f154,f196,f189,f110])).

fof(f852,plain,
    ( spl11_92
    | spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f816,f188,f160,f153,f139,f850])).

fof(f850,plain,
    ( spl11_92
  <=> k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f816,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(unit_resulting_resolution,[],[f140,f161,f154,f189,f189,f110])).

fof(f738,plain,
    ( spl11_90
    | spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f446,f206,f195,f139,f736])).

fof(f736,plain,
    ( spl11_90
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK7(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f206,plain,
    ( spl11_18
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f446,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK7(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f196,f120,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_k2_lattices)).

fof(f120,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',existence_m1_subset_1)).

fof(f207,plain,
    ( l1_lattices(sK0)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f731,plain,
    ( spl11_88
    | spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f445,f206,f188,f139,f729])).

fof(f729,plain,
    ( spl11_88
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK7(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f445,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK7(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f189,f120,f126])).

fof(f724,plain,
    ( spl11_86
    | spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f444,f206,f195,f139,f722])).

fof(f722,plain,
    ( spl11_86
  <=> m1_subset_1(k2_lattices(sK0,sK7(u1_struct_0(sK0)),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f444,plain,
    ( m1_subset_1(k2_lattices(sK0,sK7(u1_struct_0(sK0)),sK2),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f120,f196,f126])).

fof(f716,plain,
    ( ~ spl11_85
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | spl11_39 ),
    inference(avatar_split_clause,[],[f709,f282,f213,f195,f188,f139,f714])).

fof(f282,plain,
    ( spl11_39
  <=> ~ r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f709,plain,
    ( k1_lattices(sK0,sK1,sK2) != sK2
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20
    | ~ spl11_39 ),
    inference(unit_resulting_resolution,[],[f140,f214,f189,f283,f196,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f283,plain,
    ( ~ r1_lattices(sK0,sK1,sK2)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f282])).

fof(f708,plain,
    ( spl11_82
    | spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f441,f206,f188,f139,f706])).

fof(f706,plain,
    ( spl11_82
  <=> m1_subset_1(k2_lattices(sK0,sK7(u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f441,plain,
    ( m1_subset_1(k2_lattices(sK0,sK7(u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f120,f189,f126])).

fof(f565,plain,
    ( spl11_80
    | spl11_1
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f495,f213,f195,f139,f563])).

fof(f563,plain,
    ( spl11_80
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f495,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f140,f214,f196,f196,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_k1_lattices)).

fof(f558,plain,
    ( spl11_78
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f494,f213,f195,f188,f139,f556])).

fof(f556,plain,
    ( spl11_78
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f494,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f140,f214,f189,f196,f127])).

fof(f551,plain,
    ( spl11_76
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f490,f213,f195,f188,f139,f549])).

fof(f549,plain,
    ( spl11_76
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f490,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f140,f214,f196,f189,f127])).

fof(f544,plain,
    ( spl11_74
    | spl11_1
    | ~ spl11_14
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f489,f213,f188,f139,f542])).

fof(f542,plain,
    ( spl11_74
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f489,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f140,f214,f189,f189,f127])).

fof(f470,plain,
    ( spl11_72
    | spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f443,f206,f195,f139,f468])).

fof(f468,plain,
    ( spl11_72
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f443,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f196,f196,f126])).

fof(f463,plain,
    ( spl11_70
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f440,f206,f195,f188,f139,f461])).

fof(f461,plain,
    ( spl11_70
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f440,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f196,f189,f126])).

fof(f456,plain,
    ( spl11_68
    | spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f439,f206,f188,f139,f454])).

fof(f454,plain,
    ( spl11_68
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f439,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f140,f207,f189,f189,f126])).

fof(f435,plain,
    ( ~ spl11_67
    | ~ spl11_62 ),
    inference(avatar_split_clause,[],[f427,f417,f433])).

fof(f433,plain,
    ( spl11_67
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f417,plain,
    ( spl11_62
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f427,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u1_lattices(sK0))
    | ~ spl11_62 ),
    inference(unit_resulting_resolution,[],[f418,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f303,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',t5_subset)).

fof(f303,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f302,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',t4_subset)).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f280])).

fof(f280,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f279,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',t2_subset)).

fof(f279,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f123,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',antisymmetry_r2_hidden)).

fof(f418,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl11_62 ),
    inference(avatar_component_clause,[],[f417])).

fof(f426,plain,
    ( spl11_64
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f376,f213,f424])).

fof(f424,plain,
    ( spl11_64
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f376,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f214,f109])).

fof(f109,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_u2_lattices)).

fof(f419,plain,
    ( spl11_62
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f358,f206,f417])).

fof(f358,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f207,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_u1_lattices)).

fof(f411,plain,
    ( ~ spl11_61
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f403,f390,f409])).

fof(f409,plain,
    ( spl11_61
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)),u2_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f390,plain,
    ( spl11_56
  <=> m1_subset_1(u2_lattices(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f403,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)),u2_lattices(sK10))
    | ~ spl11_56 ),
    inference(unit_resulting_resolution,[],[f391,f304])).

fof(f391,plain,
    ( m1_subset_1(u2_lattices(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f390])).

fof(f401,plain,
    ( ~ spl11_59
    | ~ spl11_54 ),
    inference(avatar_split_clause,[],[f393,f383,f399])).

fof(f399,plain,
    ( spl11_59
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9)),u1_lattices(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f383,plain,
    ( spl11_54
  <=> m1_subset_1(u1_lattices(sK9),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f393,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9)),u1_lattices(sK9))
    | ~ spl11_54 ),
    inference(unit_resulting_resolution,[],[f384,f304])).

fof(f384,plain,
    ( m1_subset_1(u1_lattices(sK9),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))))
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f383])).

fof(f392,plain,
    ( spl11_56
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f375,f181,f390])).

fof(f181,plain,
    ( spl11_12
  <=> l2_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f375,plain,
    ( m1_subset_1(u2_lattices(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))))
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f182,f109])).

fof(f182,plain,
    ( l2_lattices(sK10)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f385,plain,
    ( spl11_54
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f357,f174,f383])).

fof(f174,plain,
    ( spl11_10
  <=> l1_lattices(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f357,plain,
    ( m1_subset_1(u1_lattices(sK9),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))))
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f175,f106])).

fof(f175,plain,
    ( l1_lattices(sK9)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f374,plain,
    ( spl11_52
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f335,f227,f372])).

fof(f372,plain,
    ( spl11_52
  <=> v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f227,plain,
    ( spl11_24
  <=> l2_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f335,plain,
    ( v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))
    | ~ spl11_24 ),
    inference(unit_resulting_resolution,[],[f228,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f228,plain,
    ( l2_lattices(sK8)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f367,plain,
    ( spl11_50
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f325,f220,f365])).

fof(f365,plain,
    ( spl11_50
  <=> v1_funct_2(u1_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f220,plain,
    ( spl11_22
  <=> l1_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f325,plain,
    ( v1_funct_2(u1_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))
    | ~ spl11_22 ),
    inference(unit_resulting_resolution,[],[f221,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f221,plain,
    ( l1_lattices(sK8)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f356,plain,
    ( spl11_48
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f334,f213,f354])).

fof(f354,plain,
    ( spl11_48
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f334,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f214,f108])).

fof(f349,plain,
    ( spl11_46
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f324,f206,f347])).

fof(f347,plain,
    ( spl11_46
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f324,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f207,f105])).

fof(f342,plain,
    ( spl11_44
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f333,f181,f340])).

fof(f340,plain,
    ( spl11_44
  <=> v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f333,plain,
    ( v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f182,f108])).

fof(f332,plain,
    ( spl11_42
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f323,f174,f330])).

fof(f330,plain,
    ( spl11_42
  <=> v1_funct_2(u1_lattices(sK9),k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f323,plain,
    ( v1_funct_2(u1_lattices(sK9),k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK9)),u1_struct_0(sK9))
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f175,f105])).

fof(f296,plain,
    ( ~ spl11_39
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f295,f291,f282])).

fof(f295,plain,
    ( ~ r1_lattices(sK0,sK1,sK2)
    | ~ spl11_40 ),
    inference(trivial_inequality_removal,[],[f294])).

fof(f294,plain,
    ( sK1 != sK1
    | ~ r1_lattices(sK0,sK1,sK2)
    | ~ spl11_40 ),
    inference(backward_demodulation,[],[f292,f100])).

fof(f100,plain,
    ( k2_lattices(sK0,sK1,sK2) != sK1
    | ~ r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ( k2_lattices(sK0,sK1,sK2) != sK1
      | ~ r1_lattices(sK0,sK1,sK2) )
    & ( k2_lattices(sK0,sK1,sK2) = sK1
      | r1_lattices(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f69,f72,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_lattices(X0,X1,X2) != X1
                  | ~ r1_lattices(X0,X1,X2) )
                & ( k2_lattices(X0,X1,X2) = X1
                  | r1_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(sK0,X1,X2) != X1
                | ~ r1_lattices(sK0,X1,X2) )
              & ( k2_lattices(sK0,X1,X2) = X1
                | r1_lattices(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( k2_lattices(X0,sK1,X2) != sK1
              | ~ r1_lattices(X0,sK1,X2) )
            & ( k2_lattices(X0,sK1,X2) = sK1
              | r1_lattices(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X1,X2) != X1
            | ~ r1_lattices(X0,X1,X2) )
          & ( k2_lattices(X0,X1,X2) = X1
            | r1_lattices(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,X1,sK2) != X1
          | ~ r1_lattices(X0,X1,sK2) )
        & ( k2_lattices(X0,X1,sK2) = X1
          | r1_lattices(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',t21_lattices)).

fof(f293,plain,
    ( spl11_38
    | spl11_40 ),
    inference(avatar_split_clause,[],[f99,f291,f285])).

fof(f99,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1
    | r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f277,plain,
    ( spl11_36
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f235,f227,f275])).

fof(f275,plain,
    ( spl11_36
  <=> v1_funct_1(u2_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f235,plain,
    ( v1_funct_1(u2_lattices(sK8))
    | ~ spl11_24 ),
    inference(unit_resulting_resolution,[],[f228,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f270,plain,
    ( spl11_34
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f232,f220,f268])).

fof(f268,plain,
    ( spl11_34
  <=> v1_funct_1(u1_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f232,plain,
    ( v1_funct_1(u1_lattices(sK8))
    | ~ spl11_22 ),
    inference(unit_resulting_resolution,[],[f221,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f263,plain,
    ( spl11_32
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f234,f213,f261])).

fof(f261,plain,
    ( spl11_32
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f234,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f214,f107])).

fof(f256,plain,
    ( spl11_30
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f231,f206,f254])).

fof(f254,plain,
    ( spl11_30
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f231,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f207,f104])).

fof(f249,plain,
    ( spl11_28
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f233,f181,f247])).

fof(f247,plain,
    ( spl11_28
  <=> v1_funct_1(u2_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f233,plain,
    ( v1_funct_1(u2_lattices(sK10))
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f182,f107])).

fof(f242,plain,
    ( spl11_26
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f230,f174,f240])).

fof(f240,plain,
    ( spl11_26
  <=> v1_funct_1(u1_lattices(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f230,plain,
    ( v1_funct_1(u1_lattices(sK9))
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f175,f104])).

fof(f229,plain,
    ( spl11_24
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f201,f167,f227])).

fof(f167,plain,
    ( spl11_8
  <=> l3_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f201,plain,
    ( l2_lattices(sK8)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f168,f103])).

fof(f103,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_l3_lattices)).

fof(f168,plain,
    ( l3_lattices(sK8)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f222,plain,
    ( spl11_22
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f199,f167,f220])).

fof(f199,plain,
    ( l1_lattices(sK8)
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f168,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f215,plain,
    ( spl11_20
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f200,f160,f213])).

fof(f200,plain,
    ( l2_lattices(sK0)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f161,f103])).

fof(f208,plain,
    ( spl11_18
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f198,f160,f206])).

fof(f198,plain,
    ( l1_lattices(sK0)
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f161,f102])).

fof(f197,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f98,f195])).

fof(f98,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f190,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f97,f188])).

fof(f97,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f183,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f134,f181])).

fof(f134,plain,(
    l2_lattices(sK10) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    l2_lattices(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f24,f91])).

fof(f91,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK10) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',existence_l2_lattices)).

fof(f176,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f133,f174])).

fof(f133,plain,(
    l1_lattices(sK9) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    l1_lattices(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f89])).

fof(f89,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK9) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',existence_l1_lattices)).

fof(f169,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f132,f167])).

fof(f132,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    l3_lattices(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f87])).

fof(f87,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK8) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',existence_l3_lattices)).

fof(f162,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f96,f160])).

fof(f96,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f155,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f95,f153])).

fof(f95,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f148,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f94,f146])).

fof(f94,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f141,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f93,f139])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
