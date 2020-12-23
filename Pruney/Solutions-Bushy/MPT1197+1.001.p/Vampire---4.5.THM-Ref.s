%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1197+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 241 expanded)
%              Number of leaves         :   27 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  409 ( 965 expanded)
%              Number of equality atoms :   43 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f90,f96,f115,f131,f151,f156,f177,f202,f406])).

fof(f406,plain,
    ( spl5_7
    | ~ spl5_9
    | ~ spl5_22
    | ~ spl5_3
    | spl5_1
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f404,f199,f51,f61,f174,f93,f81])).

fof(f81,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( spl5_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f174,plain,
    ( spl5_22
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f61,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( spl5_1
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f199,plain,
    ( spl5_25
  <=> sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f404,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25 ),
    inference(trivial_inequality_removal,[],[f403])).

fof(f403,plain,
    ( sK1 != sK1
    | r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25 ),
    inference(superposition,[],[f40,f201])).

fof(f201,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f199])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f202,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f197,f148,f81,f71,f66,f61,f56,f199])).

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

fof(f148,plain,
    ( spl5_17
  <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f197,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_7
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f188,f150])).

fof(f150,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f188,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

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

fof(f177,plain,
    ( spl5_22
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f172,f153,f112,f174])).

fof(f112,plain,
    ( spl5_12
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f153,plain,
    ( spl5_18
  <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f172,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f114,f155])).

fof(f155,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f114,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f156,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f137,f87,f81,f76,f61,f56,f153])).

fof(f76,plain,
    ( spl5_6
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f87,plain,
    ( spl5_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f137,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f78,f89,f63,f58,f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f89,plain,
    ( l1_lattices(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f78,plain,
    ( v6_lattices(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f151,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f146,f127,f87,f81,f76,f61,f56,f148])).

fof(f127,plain,
    ( spl5_14
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f146,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f138,f129])).

fof(f129,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f138,plain,
    ( k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f78,f89,f58,f63,f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f115,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f98,f87,f81,f61,f56,f112])).

fof(f98,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f83,f89,f63,f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

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
