%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1658+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 175 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 909 expanded)
%              Number of equality atoms :   31 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f60,f65,f71,f77,f85,f94,f110,f111])).

fof(f111,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_13
    | spl3_11 ),
    inference(avatar_split_clause,[],[f102,f91,f105,f68,f42,f47,f52,f57,f62])).

fof(f62,plain,
    ( spl3_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f57,plain,
    ( spl3_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f52,plain,
    ( spl3_5
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( spl3_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_8
  <=> m1_subset_1(sK2(sK0,sK1,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f105,plain,
    ( spl3_13
  <=> r1_lattice3(sK0,sK1,sK2(sK0,sK1,k4_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f91,plain,
    ( spl3_11
  <=> r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,k4_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f102,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(resolution,[],[f93,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattice3(X0,X1,X2)
                  | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

fof(f93,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f110,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_2
    | spl3_13
    | spl3_1
    | spl3_11 ),
    inference(avatar_split_clause,[],[f101,f91,f32,f105,f37,f47,f62])).

fof(f37,plain,
    ( spl3_2
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_1
  <=> k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | r1_lattice3(sK0,sK1,sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(resolution,[],[f93,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f94,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f89,f83,f68,f91,f32])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f89,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2(sK0,sK1,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f80,f75,f37,f83,f42,f47,f52,f57,f62])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0)
        | ~ r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,sK2(sK0,X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f78,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
        | ~ r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f76,f39])).

fof(f39,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X1)
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | ~ r1_lattice3(sK0,X1,sK2(sK0,X1,X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl3_7
    | spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f73,f47,f75,f62])).

% (32044)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | ~ r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
        | ~ r2_yellow_0(sK0,X1)
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f28,f49])).

fof(f49,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( spl3_8
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f66,f62,f47,f37,f32,f68])).

fof(f66,plain,
    ( m1_subset_1(sK2(sK0,sK1,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f64,f49,f39,f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f64,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f19,f62])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    & r2_yellow_0(sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
            & r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,k4_waybel_0(sK0,X1))
          & r2_yellow_0(sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,k4_waybel_0(sK0,X1))
        & r2_yellow_0(sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
      & r2_yellow_0(sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
          & r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
          & r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (32046)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_yellow_0(X0,X1)
             => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_0)).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f57])).

fof(f20,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f32])).

fof(f25,plain,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
