%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 305 expanded)
%              Number of leaves         :   29 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  638 (1324 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f76,f95,f100,f102,f105,f115,f125,f129,f133,f139,f151,f237,f239,f245,f255,f257,f259])).

fof(f259,plain,
    ( spl3_2
    | spl3_3
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f258,f148,f112,f122,f88,f234,f230,f226,f80,f72])).

fof(f72,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,
    ( spl3_3
  <=> v2_struct_0(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f226,plain,
    ( spl3_13
  <=> v6_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f230,plain,
    ( spl3_14
  <=> v8_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f234,plain,
    ( spl3_15
  <=> v9_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f88,plain,
    ( spl3_5
  <=> l3_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f122,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f112,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f148,plain,
    ( spl3_12
  <=> r3_lattices(k1_lattice3(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f258,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f149,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v9_lattices(k1_lattice3(X0))
      | ~ v8_lattices(k1_lattice3(X0))
      | ~ v6_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0))
      | r1_tarski(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v9_lattices(k1_lattice3(X0))
      | ~ v8_lattices(k1_lattice3(X0))
      | ~ v6_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(k1_lattice3(X0),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_lattices(k1_lattice3(X0),X1,X2)
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_lattices(k1_lattice3(X0),X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f149,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f257,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_9
    | spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f256,f68,f148,f112,f122,f88,f84,f80])).

fof(f84,plain,
    ( spl3_4
  <=> v10_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f68,plain,
    ( spl3_1
  <=> r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f256,plain,
    ( r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f69,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k3_lattice3(X0),X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f157,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1)
      | r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1)
      | r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f56,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_lattices(X0,X1,X2)
                  | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(f69,plain,
    ( r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f255,plain,
    ( ~ spl3_5
    | spl3_3
    | ~ spl3_4
    | spl3_15 ),
    inference(avatar_split_clause,[],[f254,f234,f84,f80,f88])).

fof(f254,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | spl3_15 ),
    inference(resolution,[],[f236,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f236,plain,
    ( ~ v9_lattices(k1_lattice3(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f234])).

fof(f245,plain,
    ( ~ spl3_5
    | spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_split_clause,[],[f244,f230,f84,f80,f88])).

fof(f244,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | spl3_14 ),
    inference(resolution,[],[f232,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f232,plain,
    ( ~ v8_lattices(k1_lattice3(sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f230])).

fof(f239,plain,
    ( ~ spl3_5
    | spl3_3
    | ~ spl3_4
    | spl3_13 ),
    inference(avatar_split_clause,[],[f238,f226,f84,f80,f88])).

fof(f238,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ l3_lattices(k1_lattice3(sK0))
    | spl3_13 ),
    inference(resolution,[],[f228,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f228,plain,
    ( ~ v6_lattices(k1_lattice3(sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f226])).

fof(f237,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_9
    | spl3_12 ),
    inference(avatar_split_clause,[],[f218,f148,f112,f122,f88,f234,f230,f226,f80,f72])).

fof(f218,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v9_lattices(k1_lattice3(sK0))
    | ~ v8_lattices(k1_lattice3(sK0))
    | ~ v6_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ r1_tarski(sK1,sK2)
    | spl3_12 ),
    inference(resolution,[],[f137,f150])).

fof(f150,plain,
    ( ~ r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v9_lattices(k1_lattice3(X0))
      | ~ v8_lattices(k1_lattice3(X0))
      | ~ v6_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(k1_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ l3_lattices(k1_lattice3(X0))
      | ~ v9_lattices(k1_lattice3(X0))
      | ~ v8_lattices(k1_lattice3(X0))
      | ~ v6_lattices(k1_lattice3(X0))
      | v2_struct_0(k1_lattice3(X0))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(k1_lattice3(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f151,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_9
    | ~ spl3_12
    | spl3_1 ),
    inference(avatar_split_clause,[],[f146,f68,f148,f112,f122,f88,f84,f80])).

fof(f146,plain,
    ( ~ r3_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | spl3_1 ),
    inference(resolution,[],[f145,f70])).

fof(f70,plain,
    ( ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f142,f54])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1)
      | ~ r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1)
      | ~ r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f55,f54])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f139,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r3_orders_2(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
          & ( r1_tarski(sK1,X2)
            | r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
        & ( r1_tarski(sK1,X2)
          | r3_orders_2(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
      & ( r1_tarski(sK1,sK2)
        | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r3_orders_2(k3_yellow_1(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_1)).

fof(f120,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f133,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f47])).

fof(f47,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f82,plain,
    ( v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f129,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f110,f65])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f125,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10
    | spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f116,f97,f122,f118,f88,f84,f80])).

fof(f97,plain,
    ( spl3_7
  <=> sK1 = k5_lattice3(k1_lattice3(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f116,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f60,f99])).

fof(f99,plain,
    ( sK1 = k5_lattice3(k1_lattice3(sK0),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(f115,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f106,f92,f112,f108,f88,f84,f80])).

fof(f92,plain,
    ( spl3_6
  <=> sK2 = k5_lattice3(k1_lattice3(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f106,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f60,f94])).

fof(f94,plain,
    ( sK2 = k5_lattice3(k1_lattice3(sK0),sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f105,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f90,f49])).

fof(f49,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f90,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f102,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f86,plain,
    ( ~ v10_lattices(k1_lattice3(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f78,f97,f88,f84,f80])).

fof(f78,plain,
    ( sK1 = k5_lattice3(k1_lattice3(sK0),sK1)
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f57,f66])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | k5_lattice3(X0,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(f95,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f77,f92,f88,f84,f80])).

fof(f77,plain,
    ( sK2 = k5_lattice3(k1_lattice3(sK0),sK2)
    | ~ l3_lattices(k1_lattice3(sK0))
    | ~ v10_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f57,f65])).

fof(f76,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f64,f72,f68])).

fof(f64,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f63,f72,f68])).

fof(f63,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:47:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (32308)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.43  % (32299)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.43  % (32299)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f260,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f75,f76,f95,f100,f102,f105,f115,f125,f129,f133,f139,f151,f237,f239,f245,f255,f257,f259])).
% 0.20/0.43  fof(f259,plain,(
% 0.20/0.43    spl3_2 | spl3_3 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_9 | ~spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f258,f148,f112,f122,f88,f234,f230,f226,f80,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl3_3 <=> v2_struct_0(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    spl3_13 <=> v6_lattices(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f230,plain,(
% 0.20/0.43    spl3_14 <=> v8_lattices(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.43  fof(f234,plain,(
% 0.20/0.43    spl3_15 <=> v9_lattices(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl3_5 <=> l3_lattices(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl3_11 <=> m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl3_9 <=> m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    spl3_12 <=> r3_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f258,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l3_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | r1_tarski(sK1,sK2) | ~spl3_12),
% 0.20/0.43    inference(resolution,[],[f149,f131])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~l3_lattices(k1_lattice3(X0)) | ~v9_lattices(k1_lattice3(X0)) | ~v8_lattices(k1_lattice3(X0)) | ~v6_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f130])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~l3_lattices(k1_lattice3(X0)) | ~v9_lattices(k1_lattice3(X0)) | ~v8_lattices(k1_lattice3(X0)) | ~v6_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.20/0.43    inference(resolution,[],[f61,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_lattices(k1_lattice3(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (((r1_lattices(k1_lattice3(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.20/0.43    inference(nnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f148])).
% 0.20/0.43  fof(f257,plain,(
% 0.20/0.43    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_9 | spl3_12 | ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f256,f68,f148,f112,f122,f88,f84,f80])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl3_4 <=> v10_lattices(k1_lattice3(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl3_1 <=> r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f256,plain,(
% 0.20/0.43    r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~spl3_1),
% 0.20/0.43    inference(resolution,[],[f69,f171])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_orders_2(k3_lattice3(X0),X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.43  fof(f170,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_orders_2(k3_lattice3(X0),X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(superposition,[],[f157,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1) | r3_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1) | r3_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(superposition,[],[f56,f54])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (((r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | ~spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f68])).
% 0.20/0.43  fof(f255,plain,(
% 0.20/0.43    ~spl3_5 | spl3_3 | ~spl3_4 | spl3_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f254,f234,f84,f80,f88])).
% 0.20/0.43  fof(f254,plain,(
% 0.20/0.43    ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | spl3_15),
% 0.20/0.43    inference(resolution,[],[f236,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.43    inference(flattening,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.43  fof(f236,plain,(
% 0.20/0.43    ~v9_lattices(k1_lattice3(sK0)) | spl3_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f234])).
% 0.20/0.43  fof(f245,plain,(
% 0.20/0.43    ~spl3_5 | spl3_3 | ~spl3_4 | spl3_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f244,f230,f84,f80,f88])).
% 0.20/0.43  fof(f244,plain,(
% 0.20/0.43    ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | spl3_14),
% 0.20/0.43    inference(resolution,[],[f232,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    ~v8_lattices(k1_lattice3(sK0)) | spl3_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f230])).
% 0.20/0.43  fof(f239,plain,(
% 0.20/0.43    ~spl3_5 | spl3_3 | ~spl3_4 | spl3_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f238,f226,f84,f80,f88])).
% 0.20/0.43  fof(f238,plain,(
% 0.20/0.43    ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~l3_lattices(k1_lattice3(sK0)) | spl3_13),
% 0.20/0.43    inference(resolution,[],[f228,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    ~v6_lattices(k1_lattice3(sK0)) | spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f226])).
% 0.20/0.43  fof(f237,plain,(
% 0.20/0.43    ~spl3_2 | spl3_3 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_9 | spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f218,f148,f112,f122,f88,f234,f230,f226,f80,f72])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l3_lattices(k1_lattice3(sK0)) | ~v9_lattices(k1_lattice3(sK0)) | ~v8_lattices(k1_lattice3(sK0)) | ~v6_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~r1_tarski(sK1,sK2) | spl3_12),
% 0.20/0.43    inference(resolution,[],[f137,f150])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    ~r3_lattices(k1_lattice3(sK0),sK1,sK2) | spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f148])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~l3_lattices(k1_lattice3(X0)) | ~v9_lattices(k1_lattice3(X0)) | ~v8_lattices(k1_lattice3(X0)) | ~v6_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0)) | ~r1_tarski(X1,X2)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_lattices(k1_lattice3(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | ~l3_lattices(k1_lattice3(X0)) | ~v9_lattices(k1_lattice3(X0)) | ~v8_lattices(k1_lattice3(X0)) | ~v6_lattices(k1_lattice3(X0)) | v2_struct_0(k1_lattice3(X0)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.20/0.43    inference(resolution,[],[f62,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_lattices(k1_lattice3(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_9 | ~spl3_12 | spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f146,f68,f148,f112,f122,f88,f84,f80])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    ~r3_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | spl3_1),
% 0.20/0.43    inference(resolution,[],[f145,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f68])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f144])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(superposition,[],[f142,f54])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1) | ~r3_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X2),X1) | ~r3_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(superposition,[],[f55,f54])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f39])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    spl3_10),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    $false | spl3_10),
% 0.20/0.43    inference(resolution,[],[f120,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ((~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ? [X2] : ((~r1_tarski(sK1,X2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r3_orders_2(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.20/0.44    inference(flattening,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r3_orders_2(k3_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k3_yellow_1(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.20/0.44    inference(nnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ? [X0,X1] : (? [X2] : ((r3_orders_2(k3_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.20/0.44    inference(negated_conjecture,[],[f12])).
% 0.20/0.44  fof(f12,conjecture,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r3_orders_2(k3_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_1)).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | spl3_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f118])).
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    spl3_10 <=> m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    ~spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.44  fof(f132,plain,(
% 0.20/0.44    $false | ~spl3_3),
% 0.20/0.44    inference(resolution,[],[f82,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    v2_struct_0(k1_lattice3(sK0)) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f80])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl3_8),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    $false | spl3_8),
% 0.20/0.44    inference(resolution,[],[f110,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.20/0.44    inference(definition_unfolding,[],[f43,f46])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f38])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | spl3_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f108])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    spl3_8 <=> m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.44  fof(f125,plain,(
% 0.20/0.44    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_10 | spl3_11 | ~spl3_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f116,f97,f122,f118,f88,f84,f80])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    spl3_7 <=> sK1 = k5_lattice3(k1_lattice3(sK0),sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~spl3_7),
% 0.20/0.44    inference(superposition,[],[f60,f99])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    sK1 = k5_lattice3(k1_lattice3(sK0),sK1) | ~spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f97])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_8 | spl3_9 | ~spl3_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f106,f92,f112,f108,f88,f84,f80])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    spl3_6 <=> sK2 = k5_lattice3(k1_lattice3(sK0),sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0)) | ~spl3_6),
% 0.20/0.44    inference(superposition,[],[f60,f94])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    sK2 = k5_lattice3(k1_lattice3(sK0),sK2) | ~spl3_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f92])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    spl3_5),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    $false | spl3_5),
% 0.20/0.44    inference(resolution,[],[f90,f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ~l3_lattices(k1_lattice3(sK0)) | spl3_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f88])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    spl3_4),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f101])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    $false | spl3_4),
% 0.20/0.44    inference(resolution,[],[f86,f48])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : v10_lattices(k1_lattice3(X0))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ~v10_lattices(k1_lattice3(sK0)) | spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f84])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    spl3_3 | ~spl3_4 | ~spl3_5 | spl3_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f78,f97,f88,f84,f80])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    sK1 = k5_lattice3(k1_lattice3(sK0),sK1) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.20/0.44    inference(resolution,[],[f57,f66])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | k5_lattice3(X0,X1) = X1 | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) => k5_lattice3(X0,X1) = X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f77,f92,f88,f84,f80])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    sK2 = k5_lattice3(k1_lattice3(sK0),sK2) | ~l3_lattices(k1_lattice3(sK0)) | ~v10_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.20/0.44    inference(resolution,[],[f57,f65])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    spl3_1 | spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f64,f72,f68])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    r1_tarski(sK1,sK2) | r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.20/0.44    inference(definition_unfolding,[],[f44,f46])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    r1_tarski(sK1,sK2) | r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f38])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ~spl3_1 | ~spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f63,f72,f68])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.20/0.44    inference(definition_unfolding,[],[f45,f46])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k3_yellow_1(sK0),sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f38])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (32299)------------------------------
% 0.20/0.44  % (32299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (32299)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (32299)Memory used [KB]: 6268
% 0.20/0.44  % (32299)Time elapsed: 0.049 s
% 0.20/0.44  % (32299)------------------------------
% 0.20/0.44  % (32299)------------------------------
% 0.20/0.44  % (32307)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.44  % (32290)Success in time 0.091 s
%------------------------------------------------------------------------------
