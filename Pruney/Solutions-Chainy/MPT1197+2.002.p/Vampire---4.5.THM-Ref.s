%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 213 expanded)
%              Number of leaves         :   25 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  389 ( 889 expanded)
%              Number of equality atoms :   40 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f90,f96,f115,f131,f152,f183,f372])).

fof(f372,plain,
    ( spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_3
    | spl5_1
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f370,f180,f51,f61,f112,f93,f81])).

fof(f81,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( spl5_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( spl5_12
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f61,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( spl5_1
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f180,plain,
    ( spl5_22
  <=> sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f370,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_22 ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,
    ( sK1 != sK1
    | r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_22 ),
    inference(superposition,[],[f40,f182])).

fof(f182,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f183,plain,
    ( spl5_22
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f178,f149,f81,f71,f66,f61,f56,f180])).

fof(f56,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,
    ( spl5_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f71,plain,
    ( spl5_5
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f149,plain,
    ( spl5_17
  <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f178,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f169,f151])).

fof(f151,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f169,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f83,f68,f73,f58,f63,f44])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f58,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f73,plain,
    ( v8_lattices(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f68,plain,
    ( l3_lattices(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f152,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f147,f127,f87,f81,f76,f61,f56,f149])).

fof(f76,plain,
    ( spl5_6
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f87,plain,
    ( spl5_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f127,plain,
    ( spl5_14
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f147,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f139,f129])).

fof(f129,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f139,plain,
    ( k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f78,f89,f58,f63,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f89,plain,
    ( l1_lattices(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f78,plain,
    ( v6_lattices(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f131,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f122,f87,f81,f76,f61,f56,f127])).

fof(f122,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f78,f89,f63,f58,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f115,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f98,f87,f81,f76,f61,f56,f112])).

fof(f98,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f78,f89,f63,f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f96,plain,
    ( spl5_9
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f91,f66,f93])).

fof(f91,plain,
    ( l2_lattices(sK0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f90,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f85,f66,f87])).

fof(f85,plain,
    ( l1_lattices(sK0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f79,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f51])).

fof(f38,plain,(
    ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:36:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (20750)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (20752)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (20765)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (20749)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (20750)Refutation not found, incomplete strategy% (20750)------------------------------
% 0.21/0.51  % (20750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20750)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20750)Memory used [KB]: 10490
% 0.21/0.51  % (20750)Time elapsed: 0.091 s
% 0.21/0.51  % (20750)------------------------------
% 0.21/0.51  % (20750)------------------------------
% 0.21/0.51  % (20747)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (20753)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (20763)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (20757)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (20768)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (20769)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (20753)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f90,f96,f115,f131,f152,f183,f372])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    spl5_7 | ~spl5_9 | ~spl5_12 | ~spl5_3 | spl5_1 | ~spl5_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f370,f180,f51,f61,f112,f93,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_7 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl5_9 <=> l2_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl5_12 <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl5_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl5_1 <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    spl5_22 <=> sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~spl5_22),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f369])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    sK1 != sK1 | r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~spl5_22),
% 0.21/0.52    inference(superposition,[],[f40,f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) | ~spl5_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f180])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl5_22 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_7 | ~spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f178,f149,f81,f71,f66,f61,f56,f180])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_4 <=> l3_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl5_5 <=> v8_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl5_17 <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_7 | ~spl5_17)),
% 0.21/0.52    inference(forward_demodulation,[],[f169,f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) | ~spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f83,f68,f73,f58,f63,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (((v8_lattices(X0) | ((sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(rectify,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v8_lattices(sK0) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    l3_lattices(sK0) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl5_17 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8 | ~spl5_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f147,f127,f87,f81,f76,f61,f56,f149])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl5_6 <=> v6_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl5_8 <=> l1_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl5_14 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8 | ~spl5_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f139,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f83,f78,f89,f58,f63,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v6_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    l1_lattices(sK0) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v6_lattices(sK0) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl5_14 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f122,f87,f81,f76,f61,f56,f127])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f83,f78,f89,f63,f58,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v6_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl5_12 | ~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f98,f87,f81,f76,f61,f56,f112])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f83,f78,f89,f63,f58,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl5_9 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f91,f66,f93])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    l2_lattices(sK0) | ~spl5_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f68,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl5_8 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f85,f66,f87])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    l1_lattices(sK0) | ~spl5_4),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f68,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f81])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ((~r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f24,f23,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,k4_lattices(X0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (~r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X2] : (~r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,k4_lattices(X0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,k4_lattices(X0,X1,X2),X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f76])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v6_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v8_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f66])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    l3_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f61])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f56])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f51])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20753)------------------------------
% 0.21/0.52  % (20753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20753)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20753)Memory used [KB]: 10874
% 0.21/0.52  % (20753)Time elapsed: 0.071 s
% 0.21/0.52  % (20753)------------------------------
% 0.21/0.52  % (20753)------------------------------
% 0.21/0.52  % (20748)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (20759)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (20757)Refutation not found, incomplete strategy% (20757)------------------------------
% 0.21/0.52  % (20757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20757)Memory used [KB]: 10618
% 0.21/0.52  % (20757)Time elapsed: 0.109 s
% 0.21/0.52  % (20757)------------------------------
% 0.21/0.52  % (20757)------------------------------
% 0.21/0.52  % (20751)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (20770)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (20756)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (20762)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (20770)Refutation not found, incomplete strategy% (20770)------------------------------
% 0.21/0.52  % (20770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20770)Memory used [KB]: 10618
% 0.21/0.52  % (20770)Time elapsed: 0.094 s
% 0.21/0.52  % (20770)------------------------------
% 0.21/0.52  % (20770)------------------------------
% 0.21/0.52  % (20758)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (20761)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (20755)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.53  % (20767)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (20754)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (20755)Refutation not found, incomplete strategy% (20755)------------------------------
% 0.21/0.53  % (20755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20755)Memory used [KB]: 10618
% 0.21/0.53  % (20755)Time elapsed: 0.116 s
% 0.21/0.53  % (20755)------------------------------
% 0.21/0.53  % (20755)------------------------------
% 0.21/0.53  % (20760)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (20764)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.53  % (20746)Success in time 0.172 s
%------------------------------------------------------------------------------
