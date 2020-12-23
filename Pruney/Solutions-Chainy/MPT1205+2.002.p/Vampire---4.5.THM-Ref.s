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
% DateTime   : Thu Dec  3 13:10:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 217 expanded)
%              Number of leaves         :   26 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  551 (1007 expanded)
%              Number of equality atoms :   97 ( 157 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f95,f98,f104,f122,f131,f133,f142,f153,f155,f175])).

fof(f175,plain,
    ( spl3_14
    | ~ spl3_13
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f173,f151,f102,f66,f126,f129])).

fof(f129,plain,
    ( spl3_14
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( spl3_13
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f66,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( spl3_9
  <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f151,plain,
    ( spl3_17
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X2) = X2
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f173,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(superposition,[],[f161,f103])).

fof(f103,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f161,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK1) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = k1_lattices(sK0,X0,sK1) )
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f152,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f152,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X2) = X2
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) != X3 )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

% (22224)Refutation not found, incomplete strategy% (22224)------------------------------
% (22224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22224)Termination reason: Refutation not found, incomplete strategy

% (22224)Memory used [KB]: 10618
% (22224)Time elapsed: 0.072 s
% (22224)------------------------------
% (22224)------------------------------
% (22235)Refutation not found, incomplete strategy% (22235)------------------------------
% (22235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f155,plain,
    ( ~ spl3_3
    | spl3_16 ),
    inference(avatar_split_clause,[],[f154,f148,f70])).

fof(f70,plain,
    ( spl3_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f148,plain,
    ( spl3_16
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f154,plain,
    ( ~ l3_lattices(sK0)
    | spl3_16 ),
    inference(resolution,[],[f149,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f149,plain,
    ( ~ l2_lattices(sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f153,plain,
    ( spl3_6
    | ~ spl3_16
    | spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f145,f140,f151,f148,f82])).

fof(f82,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f140,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) != X0
        | r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f145,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) != X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X2) = X2
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) != X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X2) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f141,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f141,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( spl3_6
    | ~ spl3_3
    | spl3_15
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f138,f78,f140,f70,f82])).

fof(f78,plain,
    ( spl3_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | k2_lattices(sK0,X0,X1) != X0
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_5 ),
    inference(resolution,[],[f137,f79])).

fof(f79,plain,
    ( v10_lattices(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | k2_lattices(X1,X2,X0) != X2
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | k2_lattices(X1,X2,X0) != X2
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f135,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
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

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f133,plain,
    ( spl3_6
    | ~ spl3_7
    | spl3_13 ),
    inference(avatar_split_clause,[],[f132,f126,f90,f82])).

fof(f90,plain,
    ( spl3_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f132,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_13 ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f127,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f131,plain,
    ( ~ spl3_2
    | ~ spl3_13
    | ~ spl3_14
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f123,f120,f62,f129,f126,f66])).

fof(f62,plain,
    ( spl3_1
  <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f123,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_12 ),
    inference(superposition,[],[f63,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f63,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f122,plain,
    ( ~ spl3_3
    | spl3_6
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f118,f78,f120,f82,f70])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_5 ),
    inference(resolution,[],[f117,f79])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f115,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f99,f93,f66,f102])).

fof(f93,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f99,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f94,f67])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f98,plain,
    ( ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f96,f90,f70])).

fof(f96,plain,
    ( ~ l3_lattices(sK0)
    | spl3_7 ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( ~ l1_lattices(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f95,plain,
    ( spl3_6
    | ~ spl3_7
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f87,f74,f93,f90,f82])).

fof(f74,plain,
    ( spl3_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,
    ( v13_lattices(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f84,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f37,f82])).

% (22225)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k5_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f42,f62])).

% (22235)Termination reason: Refutation not found, incomplete strategy
fof(f42,plain,(
    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (22229)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (22229)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (22243)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (22228)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (22224)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22232)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (22235)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f95,f98,f104,f122,f131,f133,f142,f153,f155,f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl3_14 | ~spl3_13 | ~spl3_2 | ~spl3_9 | ~spl3_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f173,f151,f102,f66,f126,f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl3_14 <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl3_13 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl3_9 <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl3_17 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X2) = X2 | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) != X3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | (~spl3_2 | ~spl3_9 | ~spl3_17)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    k5_lattices(sK0) != k5_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | (~spl3_2 | ~spl3_9 | ~spl3_17)),
% 0.20/0.48    inference(superposition,[],[f161,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | ~spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ( ! [X0] : (k2_lattices(sK0,X0,sK1) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,X0,sK1)) ) | (~spl3_2 | ~spl3_17)),
% 0.20/0.48    inference(resolution,[],[f152,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X2) = X2 | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) != X3) ) | ~spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f151])).
% 0.20/0.48  % (22224)Refutation not found, incomplete strategy% (22224)------------------------------
% 0.20/0.48  % (22224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22224)Memory used [KB]: 10618
% 0.20/0.48  % (22224)Time elapsed: 0.072 s
% 0.20/0.48  % (22224)------------------------------
% 0.20/0.48  % (22224)------------------------------
% 0.20/0.48  % (22235)Refutation not found, incomplete strategy% (22235)------------------------------
% 0.20/0.48  % (22235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ~spl3_3 | spl3_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f154,f148,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl3_3 <=> l3_lattices(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl3_16 <=> l2_lattices(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    ~l3_lattices(sK0) | spl3_16),
% 0.20/0.48    inference(resolution,[],[f149,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    ~l2_lattices(sK0) | spl3_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f148])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    spl3_6 | ~spl3_16 | spl3_17 | ~spl3_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f145,f140,f151,f148,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl3_6 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl3_15 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) != X0 | r1_lattices(sK0,X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X2) = X2 | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl3_15),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl3_15),
% 0.20/0.48    inference(resolution,[],[f141,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f140])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    spl3_6 | ~spl3_3 | spl3_15 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f138,f78,f140,f70,f82])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl3_5 <=> v10_lattices(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) != X0 | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl3_5),
% 0.20/0.48    inference(resolution,[],[f137,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    v10_lattices(sK0) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | k2_lattices(X1,X2,X0) != X2 | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | k2_lattices(X1,X2,X0) != X2 | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.48    inference(resolution,[],[f135,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(resolution,[],[f50,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v9_lattices(X0) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl3_6 | ~spl3_7 | spl3_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f132,f126,f90,f82])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_7 <=> l1_lattices(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl3_13),
% 0.20/0.48    inference(resolution,[],[f127,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f126])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ~spl3_2 | ~spl3_13 | ~spl3_14 | spl3_1 | ~spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f123,f120,f62,f129,f126,f66])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl3_1 <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl3_12 <=> ! [X1,X0] : (k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl3_1 | ~spl3_12)),
% 0.20/0.48    inference(superposition,[],[f63,f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~spl3_3 | spl3_6 | spl3_12 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f118,f78,f120,f82,f70])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl3_5),
% 0.20/0.48    inference(resolution,[],[f117,f79])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k1_lattices(X1,X0,X2) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.48    inference(resolution,[],[f115,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.48    inference(resolution,[],[f58,f44])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl3_9 | ~spl3_2 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f99,f93,f66,f102])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl3_8 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) | (~spl3_2 | ~spl3_8)),
% 0.20/0.48    inference(resolution,[],[f94,f67])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)) ) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~spl3_3 | spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f96,f90,f70])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ~l3_lattices(sK0) | spl3_7),
% 0.20/0.48    inference(resolution,[],[f91,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ~l1_lattices(sK0) | spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl3_6 | ~spl3_7 | spl3_8 | ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f74,f93,f90,f82])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl3_4 <=> v13_lattices(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl3_4),
% 0.20/0.48    inference(resolution,[],[f86,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    v13_lattices(sK0) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f51,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(rectify,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f82])).
% 0.20/0.48  % (22225)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    (sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k3_lattices(sK0,k5_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ? [X1] : (k3_lattices(sK0,k5_lattices(sK0),X1) != X1 & m1_subset_1(X1,u1_struct_0(sK0))) => (sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f78])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v10_lattices(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f74])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v13_lattices(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f70])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    l3_lattices(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f66])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f62])).
% 0.20/0.48  % (22235)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  
% 0.20/0.48  % (22235)Memory used [KB]: 6012
% 0.20/0.48  % (22229)------------------------------
% 0.20/0.48  % (22229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22235)Time elapsed: 0.004 s
% 0.20/0.48  % (22229)Termination reason: Refutation
% 0.20/0.48  % (22235)------------------------------
% 0.20/0.48  % (22235)------------------------------
% 0.20/0.48  
% 0.20/0.48  % (22229)Memory used [KB]: 10746
% 0.20/0.48  % (22243)Refutation not found, incomplete strategy% (22243)------------------------------
% 0.20/0.48  % (22243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22243)Memory used [KB]: 10618
% 0.20/0.48  % (22243)Time elapsed: 0.073 s
% 0.20/0.48  % (22243)------------------------------
% 0.20/0.48  % (22243)------------------------------
% 0.20/0.48  % (22229)Time elapsed: 0.070 s
% 0.20/0.48  % (22229)------------------------------
% 0.20/0.48  % (22229)------------------------------
% 0.20/0.48  % (22222)Success in time 0.127 s
%------------------------------------------------------------------------------
