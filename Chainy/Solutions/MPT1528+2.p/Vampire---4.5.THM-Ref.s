%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1528+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   59 (  93 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  222 ( 326 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4486,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4253,f4258,f4263,f4272,f4429,f4434,f4483,f4485])).

fof(f4485,plain,
    ( ~ spl153_3
    | ~ spl153_24 ),
    inference(avatar_contradiction_clause,[],[f4484])).

fof(f4484,plain,
    ( $false
    | ~ spl153_3
    | ~ spl153_24 ),
    inference(subsumption_resolution,[],[f4477,f4262])).

fof(f4262,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl153_3 ),
    inference(avatar_component_clause,[],[f4260])).

fof(f4260,plain,
    ( spl153_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_3])])).

fof(f4477,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl153_24 ),
    inference(unit_resulting_resolution,[],[f4428,f3710])).

fof(f3710,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3096])).

fof(f3096,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f4428,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl153_24 ),
    inference(avatar_component_clause,[],[f4426])).

fof(f4426,plain,
    ( spl153_24
  <=> r2_hidden(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_24])])).

fof(f4483,plain,
    ( ~ spl153_3
    | ~ spl153_25 ),
    inference(avatar_contradiction_clause,[],[f4482])).

fof(f4482,plain,
    ( $false
    | ~ spl153_3
    | ~ spl153_25 ),
    inference(subsumption_resolution,[],[f4478,f4262])).

fof(f4478,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl153_25 ),
    inference(unit_resulting_resolution,[],[f4433,f3710])).

fof(f4433,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl153_25 ),
    inference(avatar_component_clause,[],[f4431])).

fof(f4431,plain,
    ( spl153_25
  <=> r2_hidden(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_25])])).

fof(f4434,plain,
    ( spl153_25
    | ~ spl153_1
    | ~ spl153_2
    | spl153_4 ),
    inference(avatar_split_clause,[],[f4357,f4265,f4255,f4250,f4431])).

fof(f4250,plain,
    ( spl153_1
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_1])])).

fof(f4255,plain,
    ( spl153_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_2])])).

fof(f4265,plain,
    ( spl153_4
  <=> r2_lattice3(sK2,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_4])])).

fof(f4357,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl153_1
    | ~ spl153_2
    | spl153_4 ),
    inference(unit_resulting_resolution,[],[f4252,f4267,f4257,f3551])).

fof(f3551,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3291])).

fof(f3291,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3289,f3290])).

fof(f3290,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3289,plain,(
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
    inference(rectify,[],[f3288])).

fof(f3288,plain,(
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
    inference(nnf_transformation,[],[f2985])).

fof(f2985,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2984])).

fof(f2984,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
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

fof(f4257,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl153_2 ),
    inference(avatar_component_clause,[],[f4255])).

fof(f4267,plain,
    ( ~ r2_lattice3(sK2,k1_xboole_0,sK3)
    | spl153_4 ),
    inference(avatar_component_clause,[],[f4265])).

fof(f4252,plain,
    ( l1_orders_2(sK2)
    | ~ spl153_1 ),
    inference(avatar_component_clause,[],[f4250])).

fof(f4429,plain,
    ( spl153_24
    | ~ spl153_1
    | ~ spl153_2
    | spl153_5 ),
    inference(avatar_split_clause,[],[f4356,f4269,f4255,f4250,f4426])).

fof(f4269,plain,
    ( spl153_5
  <=> r1_lattice3(sK2,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_5])])).

fof(f4356,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl153_1
    | ~ spl153_2
    | spl153_5 ),
    inference(unit_resulting_resolution,[],[f4252,f4271,f4257,f3545])).

fof(f3545,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3287])).

fof(f3287,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3285,f3286])).

fof(f3286,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3285,plain,(
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
    inference(rectify,[],[f3284])).

fof(f3284,plain,(
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
    inference(nnf_transformation,[],[f2981])).

fof(f2981,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2980])).

fof(f2980,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2831])).

fof(f2831,axiom,(
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

fof(f4271,plain,
    ( ~ r1_lattice3(sK2,k1_xboole_0,sK3)
    | spl153_5 ),
    inference(avatar_component_clause,[],[f4269])).

fof(f4272,plain,
    ( ~ spl153_4
    | ~ spl153_5 ),
    inference(avatar_split_clause,[],[f3536,f4269,f4265])).

fof(f3536,plain,
    ( ~ r1_lattice3(sK2,k1_xboole_0,sK3)
    | ~ r2_lattice3(sK2,k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3283,plain,
    ( ( ~ r1_lattice3(sK2,k1_xboole_0,sK3)
      | ~ r2_lattice3(sK2,k1_xboole_0,sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f2975,f3282,f3281])).

fof(f3281,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK2,k1_xboole_0,X1)
            | ~ r2_lattice3(sK2,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3282,plain,
    ( ? [X1] :
        ( ( ~ r1_lattice3(sK2,k1_xboole_0,X1)
          | ~ r2_lattice3(sK2,k1_xboole_0,X1) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ( ~ r1_lattice3(sK2,k1_xboole_0,sK3)
        | ~ r2_lattice3(sK2,k1_xboole_0,sK3) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f2975,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2969])).

fof(f2969,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f2968])).

fof(f2968,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f4263,plain,(
    spl153_3 ),
    inference(avatar_split_clause,[],[f3575,f4260])).

fof(f3575,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4258,plain,(
    spl153_2 ),
    inference(avatar_split_clause,[],[f3535,f4255])).

fof(f3535,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4253,plain,(
    spl153_1 ),
    inference(avatar_split_clause,[],[f3534,f4250])).

fof(f3534,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3283])).
%------------------------------------------------------------------------------
