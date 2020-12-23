%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t3_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 513 expanded)
%              Number of leaves         :   16 ( 166 expanded)
%              Depth                    :   30
%              Number of atoms          :  613 (3069 expanded)
%              Number of equality atoms :   59 ( 425 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f505,f511,f1033])).

fof(f1033,plain,
    ( ~ spl8_2
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1031,f486])).

fof(f486,plain,
    ( ! [X0] : r2_lattice3(sK1,X0,sK4(sK0,X0))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f485,f51])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ v3_lattice3(sK1)
    & v3_lattice3(sK0)
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_lattice3(X1)
            & v3_lattice3(X0)
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(sK0)
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ~ v3_lattice3(sK1)
        & v3_lattice3(X0)
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( ( v3_lattice3(X0)
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
             => v3_lattice3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( ( v3_lattice3(X0)
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
           => v3_lattice3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',t3_yellow_0)).

fof(f485,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK4(sK0,X0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f484,f54])).

fof(f54,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f484,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK4(sK0,X0))
        | ~ v3_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f483,f58])).

fof(f58,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK4(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK3(X0,X2))
                & r2_lattice3(X0,sK2(X0),sK3(X0,X2))
                & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK2(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK4(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK4(X0,X4))
              & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK2(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK2(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X2))
        & r2_lattice3(X0,X1,sK3(X0,X2))
        & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK4(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK4(X0,X4))
        & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',d12_lattice3)).

fof(f483,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,sK4(sK0,X1)) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f482,f51])).

fof(f482,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,sK4(sK0,X1))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f481,f54])).

fof(f481,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,sK4(sK0,X1))
        | ~ v3_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f479,f59])).

fof(f59,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK4(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f468,f51])).

fof(f468,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f467])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f404])).

fof(f404,plain,
    ( ! [X23,X21,X22] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X21),u1_orders_2(X21))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ r2_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | r2_lattice3(sK1,X22,X23)
        | ~ l1_orders_2(X21) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f102,f139])).

fof(f139,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,
    ( ! [X26,X27] :
        ( g1_orders_2(X26,X27) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X26 )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_2
  <=> ! [X27,X26] :
        ( g1_orders_2(X26,X27) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X26 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f102,plain,(
    ! [X23,X21,X22] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X21),u1_orders_2(X21))
      | ~ r2_lattice3(X21,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK1))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | r2_lattice3(sK1,X22,X23)
      | ~ l1_orders_2(X21) ) ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f52,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X23,X21,X22] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X21),u1_orders_2(X21))
      | ~ r2_lattice3(X21,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK1))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | r2_lattice3(sK1,X22,X23)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X21) ) ),
    inference(superposition,[],[f80,f53])).

fof(f53,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',t2_yellow_0)).

fof(f1031,plain,
    ( ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,sK2(sK1)))
    | ~ spl8_2
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f1030,f501])).

fof(f501,plain,
    ( m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl8_32
  <=> m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1030,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,sK2(sK1)))
    | ~ spl8_2
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f1025,f498])).

fof(f498,plain,
    ( m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl8_30
  <=> m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1025,plain,
    ( ~ m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,sK2(sK1)))
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f1024])).

fof(f1024,plain,
    ( ~ m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,sK2(sK1)))
    | ~ m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,sK2(sK1)))
    | ~ spl8_2 ),
    inference(resolution,[],[f650,f460])).

fof(f460,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2(sK1),sK3(sK1,X0))
        | ~ m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,sK2(sK1),X0) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f459,f139])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,sK2(sK1),sK3(sK1,X0))
        | ~ r2_lattice3(sK1,sK2(sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f458,f52])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,sK2(sK1),sK3(sK1,X0))
        | ~ r2_lattice3(sK1,sK2(sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f456,f55])).

fof(f55,plain,(
    ~ v3_lattice3(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK1,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,sK2(sK1),sK3(sK1,X0))
        | v3_lattice3(sK1)
        | ~ r2_lattice3(sK1,sK2(sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f455,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,sK2(X0),sK3(X0,X2))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f444,f51])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X1,X0)
        | r2_lattice3(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f395])).

fof(f395,plain,
    ( ! [X19,X20,X18] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | r2_lattice3(X18,X19,X20)
        | ~ l1_orders_2(X18) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f101,f139])).

fof(f101,plain,(
    ! [X19,X20,X18] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ r2_lattice3(sK1,X19,X20)
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(sK1))
      | r2_lattice3(X18,X19,X20)
      | ~ l1_orders_2(X18) ) ),
    inference(subsumption_resolution,[],[f89,f52])).

fof(f89,plain,(
    ! [X19,X20,X18] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ r2_lattice3(sK1,X19,X20)
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(sK1))
      | r2_lattice3(X18,X19,X20)
      | ~ l1_orders_2(X18)
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f80,f53])).

fof(f650,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,X2,sK3(sK1,sK4(sK0,X2)))
        | ~ m1_subset_1(sK3(sK1,sK4(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,X2)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f649,f139])).

fof(f649,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK1,sK4(sK0,X2)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,sK3(sK1,sK4(sK0,X2)))
        | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,X2))
        | ~ m1_subset_1(sK4(sK0,X2),u1_struct_0(sK1)) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f648,f52])).

fof(f648,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK1,sK4(sK0,X2)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,sK3(sK1,sK4(sK0,X2)))
        | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,X2))
        | ~ m1_subset_1(sK4(sK0,X2),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f646,f55])).

fof(f646,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK1,sK4(sK0,X2)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,sK3(sK1,sK4(sK0,X2)))
        | v3_lattice3(sK1)
        | ~ r2_lattice3(sK1,sK2(sK1),sK4(sK0,X2))
        | ~ m1_subset_1(sK4(sK0,X2),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f644,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X2))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f644,plain,
    ( ! [X2,X1] :
        ( r1_orders_2(sK1,sK4(sK0,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,X1) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f643,f51])).

fof(f643,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X2),X1)
        | ~ r2_lattice3(sK0,X2,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f642,f54])).

fof(f642,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X2),X1)
        | ~ r2_lattice3(sK0,X2,X1)
        | ~ v3_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f640,f58])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f639,f51])).

fof(f639,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f638,f54])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ v3_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f637])).

fof(f637,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f636,f60])).

fof(f60,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK4(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f636,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f621,f51])).

fof(f621,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f620])).

fof(f620,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f529])).

fof(f529,plain,
    ( ! [X10,X11,X9] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | r1_orders_2(sK1,X10,X11)
        | ~ l1_orders_2(X9) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f528,f139])).

fof(f528,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
        | ~ r1_orders_2(X9,X10,X11)
        | ~ m1_subset_1(X10,u1_struct_0(sK1))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | r1_orders_2(sK1,X10,X11)
        | ~ l1_orders_2(X9) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f98,f139])).

fof(f98,plain,(
    ! [X10,X11,X9] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
      | ~ r1_orders_2(X9,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | r1_orders_2(sK1,X10,X11)
      | ~ l1_orders_2(X9) ) ),
    inference(subsumption_resolution,[],[f86,f52])).

fof(f86,plain,(
    ! [X10,X11,X9] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
      | ~ r1_orders_2(X9,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | r1_orders_2(sK1,X10,X11)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X9) ) ),
    inference(superposition,[],[f78,f53])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',t1_yellow_0)).

fof(f511,plain,(
    spl8_33 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f509,f51])).

fof(f509,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f508,f54])).

fof(f508,plain,
    ( ~ v3_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_33 ),
    inference(resolution,[],[f504,f58])).

fof(f504,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl8_33
  <=> ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f505,plain,
    ( spl8_30
    | ~ spl8_33
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f492,f110,f503,f497])).

fof(f492,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f491,f139])).

fof(f491,plain,
    ( m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK1))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f490,f139])).

fof(f490,plain,
    ( m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK1))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f489,f52])).

fof(f489,plain,
    ( m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f488,f55])).

fof(f488,plain,
    ( m1_subset_1(sK3(sK1,sK4(sK0,sK2(sK1))),u1_struct_0(sK1))
    | v3_lattice3(sK1)
    | ~ m1_subset_1(sK4(sK0,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f486,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_lattice3(X0,sK2(X0),X2)
      | m1_subset_1(sK3(X0,X2),u1_struct_0(X0))
      | v3_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f117,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',dt_u1_orders_2)).

fof(f108,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_1
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f112,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f92,f110,f107])).

fof(f92,plain,(
    ! [X26,X27] :
      ( g1_orders_2(X26,X27) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X26
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f71,f53])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t3_yellow_0.p',free_g1_orders_2)).
%------------------------------------------------------------------------------
