%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 215 expanded)
%              Number of leaves         :   26 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  401 (1101 expanded)
%              Number of equality atoms :   38 (  44 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f100,f119,f132,f156,f188,f226])).

fof(f226,plain,
    ( ~ spl6_13
    | ~ spl6_3
    | spl6_1
    | ~ spl6_19
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f225,f185,f154,f51,f61,f116])).

fof(f116,plain,
    ( spl6_13
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f61,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f51,plain,
    ( spl6_1
  <=> r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f154,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( k1_lattices(sK0,X0,X1) != X1
        | r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f185,plain,
    ( spl6_23
  <=> k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f225,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_19
    | ~ spl6_23 ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_19
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f221,f187])).

fof(f187,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f221,plain,
    ( k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_19 ),
    inference(resolution,[],[f155,f53])).

fof(f53,plain,
    ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | k1_lattices(sK0,X0,X1) != X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f188,plain,
    ( spl6_23
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f183,f129,f97,f91,f86,f61,f56,f185])).

fof(f56,plain,
    ( spl6_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( spl6_8
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f91,plain,
    ( spl6_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f97,plain,
    ( spl6_10
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( spl6_15
  <=> sK1 = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f183,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f160,f131])).

fof(f131,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f160,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f93,f99,f88,f63,f63,f58,f43])).

fof(f43,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v5_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),sK5(X0))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).

fof(f27,plain,(
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
                ( k1_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

fof(f58,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f88,plain,
    ( v5_lattices(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f99,plain,
    ( l2_lattices(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f93,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f156,plain,
    ( ~ spl6_10
    | spl6_19
    | spl6_9 ),
    inference(avatar_split_clause,[],[f147,f91,f154,f97])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,X0,X1) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | r1_lattices(sK0,X0,X1) )
    | spl6_9 ),
    inference(resolution,[],[f41,f93])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f132,plain,
    ( spl6_15
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(avatar_split_clause,[],[f126,f91,f81,f76,f71,f66,f61,f129])).

fof(f66,plain,
    ( spl6_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( spl6_5
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f76,plain,
    ( spl6_6
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,
    ( spl6_7
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f126,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f93,f83,f78,f73,f68,f63,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k1_lattices(X0,X1,X1) = X1
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f68,plain,
    ( l3_lattices(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f73,plain,
    ( v9_lattices(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( v8_lattices(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f83,plain,
    ( v6_lattices(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f119,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f102,f97,f91,f61,f56,f116])).

fof(f102,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f93,f99,f63,f58,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f100,plain,
    ( spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f95,f66,f97])).

fof(f95,plain,
    ( l2_lattices(sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f94,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f31,f91])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & v5_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

fof(f89,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    v5_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f56])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f39,f51])).

% (20189)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f39,plain,(
    ~ r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20181)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.47  % (20183)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (20183)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (20200)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f89,f94,f100,f119,f132,f156,f188,f226])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~spl6_13 | ~spl6_3 | spl6_1 | ~spl6_19 | ~spl6_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f225,f185,f154,f51,f61,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl6_13 <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl6_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl6_1 <=> r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl6_19 <=> ! [X1,X0] : (k1_lattices(sK0,X0,X1) != X1 | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl6_23 <=> k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl6_1 | ~spl6_19 | ~spl6_23)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f224])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl6_1 | ~spl6_19 | ~spl6_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f221,f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~spl6_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f185])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    k1_lattices(sK0,sK1,sK2) != k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl6_1 | ~spl6_19)),
% 0.21/0.48    inference(resolution,[],[f155,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | k1_lattices(sK0,X0,X1) != X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f154])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    spl6_23 | ~spl6_2 | ~spl6_3 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f183,f129,f97,f91,f86,f61,f56,f185])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl6_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl6_8 <=> v5_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl6_9 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl6_10 <=> l2_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl6_15 <=> sK1 = k1_lattices(sK0,sK1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f160,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    sK1 = k1_lattices(sK0,sK1,sK1) | ~spl6_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) | (~spl6_2 | ~spl6_3 | ~spl6_8 | spl6_9 | ~spl6_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f93,f99,f88,f63,f63,f58,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X6,X4,X0,X5] : (~v5_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (((v5_lattices(X0) | (((k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (? [X3] : (k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k1_lattices(X0,sK3(X0),sK4(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v5_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v5_lattices(sK0) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    l2_lattices(sK0) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~spl6_10 | spl6_19 | spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f147,f91,f154,f97])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_lattices(sK0,X0,X1) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | r1_lattices(sK0,X0,X1)) ) | spl6_9),
% 0.21/0.49    inference(resolution,[],[f41,f93])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | r1_lattices(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl6_15 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f91,f81,f76,f71,f66,f61,f129])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl6_4 <=> l3_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl6_5 <=> v9_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl6_6 <=> v8_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl6_7 <=> v6_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    sK1 = k1_lattices(sK0,sK1,sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f93,f83,f78,f73,f68,f63,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v9_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k1_lattices(X0,X1,X1) = X1 | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    l3_lattices(sK0) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v9_lattices(sK0) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v8_lattices(sK0) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v6_lattices(sK0) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl6_13 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f102,f97,f91,f61,f56,f116])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f93,f99,f63,f58,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_10 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f66,f97])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    l2_lattices(sK0) | ~spl6_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f68,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f91])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ((~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & v5_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f22,f21,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v6_lattices(sK0) & v5_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~r1_lattices(sK0,X1,k1_lattices(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X2] : (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f86])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v5_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f81])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v6_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v8_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f71])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v9_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f61])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f56])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f51])).
% 0.21/0.49  % (20189)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~r1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (20183)------------------------------
% 0.21/0.50  % (20183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20183)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (20183)Memory used [KB]: 10746
% 0.21/0.50  % (20183)Time elapsed: 0.068 s
% 0.21/0.50  % (20183)------------------------------
% 0.21/0.50  % (20183)------------------------------
% 0.21/0.50  % (20173)Success in time 0.136 s
%------------------------------------------------------------------------------
