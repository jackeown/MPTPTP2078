%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t20_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:38 EDT 2019

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 733 expanded)
%              Number of leaves         :   21 ( 228 expanded)
%              Depth                    :   35
%              Number of atoms          : 1268 (8308 expanded)
%              Number of equality atoms :   34 ( 281 expanded)
%              Maximal formula depth    :   25 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f121,f9158,f9255,f9404,f9428])).

fof(f9428,plain,
    ( ~ spl10_0
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f9427])).

fof(f9427,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f9426,f117])).

fof(f117,plain,
    ( v1_lattice3(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl10_0
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f9426,plain,
    ( ~ v1_lattice3(sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f9425,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f9425,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ spl10_3
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f9424,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f9424,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f9423,f60])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        & m1_subset_1(sK2,u1_struct_0(sK0))
        & m1_subset_1(sK1,u1_struct_0(sK0)) )
      | ~ v1_lattice3(sK0) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r1_yellow_0(sK0,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v1_lattice3(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v1_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            & m1_subset_1(X1,u1_struct_0(sK0)) )
        | ~ v1_lattice3(sK0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(sK0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v1_lattice3(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_yellow_0(X0,k2_tarski(sK1,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_yellow_0(X0,k2_tarski(X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v1_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t20_yellow_0.p',t20_yellow_0)).

fof(f9423,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f9417,f61])).

fof(f61,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f9417,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f105,f531])).

fof(f531,plain,(
    ! [X4,X5,X3] :
      ( r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v1_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f530,f67])).

fof(f67,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
                  & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
                  & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
                  & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,sK6(X0,X5,X6))
                    & r1_orders_2(X0,X5,sK6(X0,X5,X6))
                    & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f48,f52,f51,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK3(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK4(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
        & r1_orders_2(X0,X2,sK5(X0,X3))
        & r1_orders_2(X0,X1,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK6(X0,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X5,X6))
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X7,X8)
                          | ~ r1_orders_2(X0,X6,X8)
                          | ~ r1_orders_2(X0,X5,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X6,X7)
                      & r1_orders_2(X0,X5,X7)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t20_yellow_0.p',d10_lattice3)).

fof(f530,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f529,f69])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f529,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ r1_orders_2(X4,X3,sK6(X4,X5,X3))
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f524,f68])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f524,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ r1_orders_2(X4,X5,sK6(X4,X5,X3))
      | ~ r1_orders_2(X4,X3,sK6(X4,X5,X3))
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | r1_yellow_0(X4,k2_tarski(X3,X5))
      | ~ r1_orders_2(X4,X5,sK6(X4,X5,X3))
      | ~ r1_orders_2(X4,X3,sK6(X4,X5,X3))
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f360,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t20_yellow_0.p',t18_yellow_0)).

fof(f360,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ v1_lattice3(X10) ) ),
    inference(subsumption_resolution,[],[f359,f67])).

fof(f359,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v1_lattice3(X10)
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f358,f69])).

fof(f358,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v1_lattice3(X10)
      | ~ r1_orders_2(X10,X11,sK6(X10,X9,X11))
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f345,f68])).

fof(f345,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK6(X10,X9,X11))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v1_lattice3(X10)
      | ~ r1_orders_2(X10,X11,sK6(X10,X9,X11))
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK6(X10,X9,X11))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ v1_lattice3(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK6(X10,X9,X11))
      | ~ r1_orders_2(X10,X11,sK6(X10,X9,X11))
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10) ) ),
    inference(resolution,[],[f268,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f268,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X6,sK7(X4,X7,X5,sK6(X4,X6,X7)))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X5))
      | ~ r1_orders_2(X4,X5,sK6(X4,X6,X7))
      | ~ m1_subset_1(sK7(X4,X7,X5,sK6(X4,X6,X7)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v1_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f267,f67])).

fof(f267,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,X6,X7))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X5))
      | ~ r1_orders_2(X4,X6,sK7(X4,X7,X5,sK6(X4,X6,X7)))
      | ~ m1_subset_1(sK7(X4,X7,X5,sK6(X4,X6,X7)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X6,X7),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f263,f69])).

fof(f263,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,X6,X7))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X5))
      | ~ r1_orders_2(X4,X6,sK7(X4,X7,X5,sK6(X4,X6,X7)))
      | ~ m1_subset_1(sK7(X4,X7,X5,sK6(X4,X6,X7)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X6,X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,X6,X7))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X5))
      | ~ r1_orders_2(X4,X6,sK7(X4,X7,X5,sK6(X4,X6,X7)))
      | ~ m1_subset_1(sK7(X4,X7,X5,sK6(X4,X6,X7)),u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X5))
      | ~ r1_orders_2(X4,X5,sK6(X4,X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,X6,X7))
      | ~ m1_subset_1(sK6(X4,X6,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f162,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f162,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_orders_2(X6,X10,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ r1_orders_2(X6,X8,sK6(X6,X9,X10))
      | ~ r1_orders_2(X6,X7,sK6(X6,X9,X10))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,X9,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6) ) ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f159,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,X8,sK6(X6,X9,X10))
      | ~ r1_orders_2(X6,X7,sK6(X6,X9,X10))
      | ~ m1_subset_1(sK6(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_orders_2(X6,X10,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ r1_orders_2(X6,X9,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,X8,sK6(X6,X9,X10))
      | ~ r1_orders_2(X6,X7,sK6(X6,X9,X10))
      | ~ m1_subset_1(sK6(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_orders_2(X6,X10,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ r1_orders_2(X6,X9,sK7(X6,X7,X8,sK6(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6)
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl10_3
  <=> ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f9404,plain,
    ( spl10_1
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f9403])).

fof(f9403,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f9402,f61])).

fof(f9402,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f9401,f102])).

fof(f102,plain,
    ( ~ v1_lattice3(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl10_1
  <=> ~ v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f9401,plain,
    ( v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_13 ),
    inference(resolution,[],[f9157,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9157,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f9156])).

fof(f9156,plain,
    ( spl10_13
  <=> ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f9255,plain,
    ( spl10_1
    | spl10_11 ),
    inference(avatar_contradiction_clause,[],[f9254])).

fof(f9254,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f9253,f61])).

fof(f9253,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f9252,f102])).

fof(f9252,plain,
    ( v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_11 ),
    inference(resolution,[],[f9154,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9154,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f9153])).

fof(f9153,plain,
    ( spl10_11
  <=> ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f9158,plain,
    ( ~ spl10_11
    | ~ spl10_13
    | spl10_1
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f9151,f119,f101,f9156,f9153])).

fof(f119,plain,
    ( spl10_8
  <=> ! [X3,X4] :
        ( r1_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f9151,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f9150,f61])).

fof(f9150,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f9149,f102])).

fof(f9149,plain,
    ( v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f9142,f60])).

fof(f9142,plain,
    ( ~ v5_orders_2(sK0)
    | v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(resolution,[],[f9113,f120])).

fof(f120,plain,
    ( ! [X4,X3] :
        ( r1_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f9113,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f9112,f71])).

fof(f9112,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f9111,f72])).

fof(f9111,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f9110,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t20_yellow_0.p',dt_k10_lattice3)).

fof(f9110,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f9109,f1899])).

fof(f1899,plain,(
    ! [X21,X19,X20] :
      ( r1_orders_2(X19,X20,k10_lattice3(X19,X21,X20))
      | ~ r1_yellow_0(X19,k2_tarski(X20,X21))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19) ) ),
    inference(duplicate_literal_removal,[],[f1796])).

fof(f1796,plain,(
    ! [X21,X19,X20] :
      ( r1_orders_2(X19,X20,k10_lattice3(X19,X21,X20))
      | ~ r1_yellow_0(X19,k2_tarski(X20,X21))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ r1_yellow_0(X19,k2_tarski(X20,X21)) ) ),
    inference(superposition,[],[f151,f1529])).

fof(f1529,plain,(
    ! [X6,X8,X7] :
      ( k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_yellow_0(X6,k2_tarski(X7,X8)) ) ),
    inference(subsumption_resolution,[],[f1528,f95])).

fof(f1528,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ m1_subset_1(k10_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f1527,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f98,f95])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1527,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,X8,k10_lattice3(X6,X7,X8))
      | ~ m1_subset_1(k10_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f1522,f151])).

fof(f1522,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,X7,k10_lattice3(X6,X7,X8))
      | ~ r1_orders_2(X6,X8,k10_lattice3(X6,X7,X8))
      | ~ m1_subset_1(k10_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(duplicate_literal_removal,[],[f1503])).

fof(f1503,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,X7,k10_lattice3(X6,X7,X8))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | k10_lattice3(X6,X7,X8) = k10_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,X7,k10_lattice3(X6,X7,X8))
      | ~ r1_orders_2(X6,X8,k10_lattice3(X6,X7,X8))
      | ~ m1_subset_1(k10_lattice3(X6,X7,X8),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(resolution,[],[f549,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f549,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK7(X0,X2,X3,k10_lattice3(X0,X1,X2)))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f548,f95])).

fof(f548,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X1,sK7(X0,X2,X3,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f547,f149])).

fof(f547,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X1,sK7(X0,X2,X3,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X1,sK7(X0,X2,X3,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f240,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f240,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,X7,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ r1_yellow_0(X3,k2_tarski(X4,X7))
      | ~ r1_orders_2(X3,X4,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k10_lattice3(X3,X4,X7) = k10_lattice3(X3,X5,X6)
      | ~ r1_orders_2(X3,X6,k10_lattice3(X3,X4,X7))
      | ~ r1_orders_2(X3,X5,k10_lattice3(X3,X4,X7))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f239,f95])).

fof(f239,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,X4,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ r1_yellow_0(X3,k2_tarski(X4,X7))
      | ~ r1_orders_2(X3,X7,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k10_lattice3(X3,X4,X7) = k10_lattice3(X3,X5,X6)
      | ~ r1_orders_2(X3,X6,k10_lattice3(X3,X4,X7))
      | ~ r1_orders_2(X3,X5,k10_lattice3(X3,X4,X7))
      | ~ m1_subset_1(k10_lattice3(X3,X4,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f235,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f235,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,X4,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)),u1_struct_0(X3))
      | ~ r1_yellow_0(X3,k2_tarski(X4,X7))
      | ~ r1_orders_2(X3,X7,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k10_lattice3(X3,X4,X7) = k10_lattice3(X3,X5,X6)
      | ~ r1_orders_2(X3,X6,k10_lattice3(X3,X4,X7))
      | ~ r1_orders_2(X3,X5,k10_lattice3(X3,X4,X7))
      | ~ m1_subset_1(k10_lattice3(X3,X4,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,X4,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)),u1_struct_0(X3))
      | ~ r1_yellow_0(X3,k2_tarski(X4,X7))
      | ~ r1_orders_2(X3,X7,sK7(X3,X5,X6,k10_lattice3(X3,X4,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k10_lattice3(X3,X4,X7) = k10_lattice3(X3,X5,X6)
      | ~ r1_orders_2(X3,X6,k10_lattice3(X3,X4,X7))
      | ~ r1_orders_2(X3,X5,k10_lattice3(X3,X4,X7))
      | ~ m1_subset_1(k10_lattice3(X3,X4,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f183,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X3,X1))
      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f97,f95])).

fof(f97,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f99,f95])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9109,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,sK4(X0),sK3(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f9072])).

fof(f9072,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,sK4(X0),sK3(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f1733,f1900])).

fof(f1900,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,X18,k10_lattice3(X16,X18,X17))
      | ~ r1_yellow_0(X16,k2_tarski(X17,X18))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16) ) ),
    inference(duplicate_literal_removal,[],[f1795])).

fof(f1795,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,X18,k10_lattice3(X16,X18,X17))
      | ~ r1_yellow_0(X16,k2_tarski(X17,X18))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ r1_yellow_0(X16,k2_tarski(X17,X18)) ) ),
    inference(superposition,[],[f149,f1529])).

fof(f1733,plain,(
    ! [X1] :
      ( ~ r1_orders_2(X1,sK4(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v1_lattice3(X1)
      | ~ r1_yellow_0(X1,k2_tarski(sK3(X1),sK4(X1)))
      | ~ r1_orders_2(X1,sK3(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(forward_demodulation,[],[f1732,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t20_yellow_0.p',commutativity_k2_tarski)).

fof(f1732,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v1_lattice3(X1)
      | ~ r1_orders_2(X1,sK4(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ r1_orders_2(X1,sK3(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1729,f72])).

fof(f1729,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ m1_subset_1(sK4(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v1_lattice3(X1)
      | ~ r1_orders_2(X1,sK4(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ r1_orders_2(X1,sK3(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1708])).

fof(f1708,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ m1_subset_1(sK4(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v1_lattice3(X1)
      | ~ r1_orders_2(X1,sK4(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ r1_orders_2(X1,sK3(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1))
      | v1_lattice3(X1)
      | ~ r1_orders_2(X1,sK4(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ r1_orders_2(X1,sK3(X1),k10_lattice3(X1,sK4(X1),sK3(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f413,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK4(X0),sK5(X0,X3))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,sK3(X0))))
      | ~ r1_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f412,f71])).

fof(f412,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,sK3(X0))))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,sK3(X0))))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,sK3(X0)))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,sK3(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f238,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK3(X0),sK5(X0,X3))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f237,f95])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f236,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(sK5(X0,k10_lattice3(X0,X1,X2)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(sK5(X0,k10_lattice3(X0,X1,X2)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,sK5(X0,k10_lattice3(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),k10_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,sK3(X0),k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f183,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,
    ( spl10_0
    | spl10_8 ),
    inference(avatar_split_clause,[],[f62,f119,f116])).

fof(f62,plain,(
    ! [X4,X3] :
      ( r1_yellow_0(sK0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v1_lattice3(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,
    ( ~ spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f63,f112,f101])).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f64,f108,f101])).

fof(f64,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f65,f104,f101])).

fof(f65,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
