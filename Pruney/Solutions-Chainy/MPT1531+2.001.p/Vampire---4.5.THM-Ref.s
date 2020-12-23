%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 341 expanded)
%              Number of leaves         :   33 ( 161 expanded)
%              Depth                    :    9
%              Number of atoms          :  476 (1445 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f91,f96,f101,f106,f112,f120,f125,f130,f153,f160,f168,f173,f178,f194,f210,f234,f256,f263,f330,f334])).

fof(f334,plain,
    ( ~ spl8_12
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f222,f170,f140])).

fof(f140,plain,
    ( spl8_12
  <=> sP7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f170,plain,
    ( spl8_17
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f222,plain,
    ( ~ sP7(sK1)
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f172,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f65,f70_D])).

fof(f70,plain,(
    ! [X2,X1] :
      ( sP7(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f70_D])).

fof(f70_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f172,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f330,plain,
    ( spl8_19
    | ~ spl8_23
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl8_19
    | ~ spl8_23
    | spl8_25 ),
    inference(subsumption_resolution,[],[f328,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl8_25
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f328,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | spl8_19
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f193,f233,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f233,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl8_23
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f193,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_19
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f263,plain,
    ( spl8_20
    | ~ spl8_14
    | spl8_19 ),
    inference(avatar_split_clause,[],[f259,f191,f150,f207])).

fof(f207,plain,
    ( spl8_20
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f150,plain,
    ( spl8_14
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f259,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_14
    | spl8_19 ),
    inference(unit_resulting_resolution,[],[f152,f193,f67])).

fof(f152,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f256,plain,
    ( ~ spl8_25
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f250,f175,f165,f103,f93,f87,f253])).

fof(f87,plain,
    ( spl8_4
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f93,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f103,plain,
    ( spl8_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f165,plain,
    ( spl8_16
  <=> r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f175,plain,
    ( spl8_18
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f250,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_16
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f105,f89,f95,f167,f177,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f177,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f167,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f95,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f89,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f105,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f234,plain,
    ( spl8_23
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f220,f170,f109,f231])).

fof(f109,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f220,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_8
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f111,f172,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f210,plain,
    ( ~ spl8_20
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f204,f127,f117,f103,f93,f82,f207])).

fof(f82,plain,
    ( spl8_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f117,plain,
    ( spl8_9
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f127,plain,
    ( spl8_11
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f204,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_9
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f105,f84,f95,f119,f129,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f129,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f119,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f84,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f194,plain,
    ( ~ spl8_19
    | ~ spl8_8
    | spl8_12 ),
    inference(avatar_split_clause,[],[f188,f140,f109,f191])).

fof(f188,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_8
    | spl8_12 ),
    inference(unit_resulting_resolution,[],[f111,f142,f70])).

fof(f142,plain,
    ( ~ sP7(sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f178,plain,
    ( spl8_18
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f161,f103,f93,f77,f175])).

fof(f77,plain,
    ( spl8_2
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f161,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f95,f79,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f173,plain,
    ( spl8_17
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f162,f103,f93,f77,f170])).

fof(f162,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f95,f79,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f168,plain,
    ( ~ spl8_16
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f163,f103,f93,f77,f165])).

fof(f163,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f95,f79,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f160,plain,
    ( ~ spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f138,f122,f140])).

fof(f122,plain,
    ( spl8_10
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f138,plain,
    ( ~ sP7(sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f124,f71])).

fof(f124,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f153,plain,
    ( spl8_14
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f134,f122,f109,f150])).

fof(f134,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f111,f124,f66])).

fof(f130,plain,
    ( spl8_11
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f113,f103,f93,f73,f127])).

fof(f73,plain,
    ( spl8_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f113,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f75,f95,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f125,plain,
    ( spl8_10
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f114,f103,f93,f73,f122])).

fof(f114,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f75,f95,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,
    ( ~ spl8_9
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f115,f103,f93,f73,f117])).

fof(f115,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f105,f75,f95,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f107,f98,f109])).

fof(f98,plain,
    ( spl8_6
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f100,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f106,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f46,f103])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
        & r2_lattice3(sK0,sK2,sK3) )
      | ( ~ r1_lattice3(sK0,sK1,sK3)
        & r1_lattice3(sK0,sK2,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(X0,X1,X3)
                    & r1_lattice3(X0,X2,X3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK0,X1,X3)
                  & r2_lattice3(sK0,X2,X3) )
                | ( ~ r1_lattice3(sK0,X1,X3)
                  & r1_lattice3(sK0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ( ( ~ r2_lattice3(sK0,X1,X3)
                & r2_lattice3(sK0,X2,X3) )
              | ( ~ r1_lattice3(sK0,X1,X3)
                & r1_lattice3(sK0,X2,X3) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_tarski(X1,X2) )
   => ( ? [X3] :
          ( ( ( ~ r2_lattice3(sK0,sK1,X3)
              & r2_lattice3(sK0,sK2,X3) )
            | ( ~ r1_lattice3(sK0,sK1,X3)
              & r1_lattice3(sK0,sK2,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ~ r2_lattice3(sK0,sK1,X3)
            & r2_lattice3(sK0,sK2,X3) )
          | ( ~ r1_lattice3(sK0,sK1,X3)
            & r1_lattice3(sK0,sK2,X3) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
          & r2_lattice3(sK0,sK2,sK3) )
        | ( ~ r1_lattice3(sK0,sK1,sK3)
          & r1_lattice3(sK0,sK2,sK3) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f101,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f49,f87,f82])).

fof(f49,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f50,f87,f73])).

fof(f50,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f51,f77,f82])).

fof(f51,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f52,f77,f73])).

fof(f52,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:56:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (16591)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (16591)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (16599)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f80,f85,f90,f91,f96,f101,f106,f112,f120,f125,f130,f153,f160,f168,f173,f178,f194,f210,f234,f256,f263,f330,f334])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~spl8_12 | ~spl8_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f222,f170,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl8_12 <=> sP7(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl8_17 <=> r2_hidden(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~sP7(sK1) | ~spl8_17),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f172,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 0.21/0.49    inference(general_splitting,[],[f65,f70_D])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X1] : (sP7(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f70_D])).
% 0.21/0.49  fof(f70_D,plain,(
% 0.21/0.49    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 0.21/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    r2_hidden(sK4(sK0,sK1,sK3),sK1) | ~spl8_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    spl8_19 | ~spl8_23 | spl8_25),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    $false | (spl8_19 | ~spl8_23 | spl8_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f328,f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK1,sK3),sK2) | spl8_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl8_25 <=> r2_hidden(sK4(sK0,sK1,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    r2_hidden(sK4(sK0,sK1,sK3),sK2) | (spl8_19 | ~spl8_23)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f193,f233,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    m1_subset_1(sK4(sK0,sK1,sK3),sK2) | ~spl8_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl8_23 <=> m1_subset_1(sK4(sK0,sK1,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | spl8_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl8_19 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    spl8_20 | ~spl8_14 | spl8_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f259,f191,f150,f207])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    spl8_20 <=> r2_hidden(sK5(sK0,sK1,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl8_14 <=> m1_subset_1(sK5(sK0,sK1,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0,sK1,sK3),sK2) | (~spl8_14 | spl8_19)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f152,f193,f67])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,sK1,sK3),sK2) | ~spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~spl8_25 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_16 | ~spl8_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f250,f175,f165,f103,f93,f87,f253])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl8_4 <=> r2_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl8_5 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl8_7 <=> l1_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl8_16 <=> r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl8_18 <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK1,sK3),sK2) | (~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_16 | ~spl8_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f105,f89,f95,f167,f177,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(rectify,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) | ~spl8_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3) | spl8_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f165])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl8_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r2_lattice3(sK0,sK2,sK3) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    l1_orders_2(sK0) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f103])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    spl8_23 | ~spl8_8 | ~spl8_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f170,f109,f231])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl8_8 <=> m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    m1_subset_1(sK4(sK0,sK1,sK3),sK2) | (~spl8_8 | ~spl8_17)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f111,f172,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK2)) | ~spl8_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~spl8_20 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_9 | ~spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f204,f127,f117,f103,f93,f82,f207])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl8_3 <=> r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl8_9 <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl8_11 <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,sK1,sK3),sK2) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_9 | ~spl8_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f105,f84,f95,f119,f129,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | spl8_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    r1_lattice3(sK0,sK2,sK3) | ~spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ~spl8_19 | ~spl8_8 | spl8_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f188,f140,f109,f191])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2) | (~spl8_8 | spl8_12)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f111,f142,f70])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~sP7(sK1) | spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl8_18 | spl8_2 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f161,f103,f93,f77,f175])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl8_2 <=> r2_lattice3(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl8_2 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f95,f79,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~r2_lattice3(sK0,sK1,sK3) | spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl8_17 | spl8_2 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f103,f93,f77,f170])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,sK3),sK1) | (spl8_2 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f95,f79,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~spl8_16 | spl8_2 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f103,f93,f77,f165])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3) | (spl8_2 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f95,f79,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK4(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~spl8_12 | ~spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f138,f122,f140])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl8_10 <=> r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~sP7(sK1) | ~spl8_10),
% 0.21/0.50    inference(resolution,[],[f124,f71])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl8_14 | ~spl8_8 | ~spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f122,f109,f150])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK0,sK1,sK3),sK2) | (~spl8_8 | ~spl8_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f111,f124,f66])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl8_11 | spl8_1 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f113,f103,f93,f73,f127])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl8_1 <=> r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl8_1 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f75,f95,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~r1_lattice3(sK0,sK1,sK3) | spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl8_10 | spl8_1 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f114,f103,f93,f73,f122])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    r2_hidden(sK5(sK0,sK1,sK3),sK1) | (spl8_1 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f75,f95,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~spl8_9 | spl8_1 | ~spl8_5 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f115,f103,f93,f73,f117])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | (spl8_1 | ~spl8_5 | ~spl8_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f105,f75,f95,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl8_8 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f98,f109])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl8_6 <=> r1_tarski(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK2)) | ~spl8_6),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f100,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f103])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ((((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0)) => (? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) & l1_orders_2(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) => (? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f98])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f93])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl8_3 | spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f87,f82])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~spl8_1 | spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f87,f73])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl8_3 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f77,f82])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ~r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl8_1 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f77,f73])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~r2_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16591)------------------------------
% 0.21/0.50  % (16591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16591)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16591)Memory used [KB]: 6268
% 0.21/0.50  % (16591)Time elapsed: 0.067 s
% 0.21/0.50  % (16591)------------------------------
% 0.21/0.50  % (16591)------------------------------
% 0.21/0.50  % (16577)Success in time 0.138 s
%------------------------------------------------------------------------------
