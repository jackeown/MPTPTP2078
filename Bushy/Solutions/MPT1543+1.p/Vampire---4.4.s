%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t21_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 1.37s
% Output     : Refutation 1.46s
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
fof(f10317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f121,f10050,f10130,f10283,f10308])).

fof(f10308,plain,
    ( ~ spl10_0
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f10307])).

fof(f10307,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10306,f117])).

fof(f117,plain,
    ( v2_lattice3(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl10_0
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f10306,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10305,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f10305,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ spl10_3
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10304,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f10304,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f10303,f60])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        & m1_subset_1(sK2,u1_struct_0(sK0))
        & m1_subset_1(sK1,u1_struct_0(sK0)) )
      | ~ v2_lattice3(sK0) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r2_yellow_0(sK0,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v2_lattice3(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v2_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(sK0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            & m1_subset_1(X1,u1_struct_0(sK0)) )
        | ~ v2_lattice3(sK0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(sK0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v2_lattice3(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK1,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v2_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t21_yellow_0.p',t21_yellow_0)).

fof(f10303,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f10297,f61])).

fof(f61,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f10297,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f105,f509])).

fof(f509,plain,(
    ! [X4,X5,X3] :
      ( r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f508,f67])).

fof(f67,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
                  & r1_orders_2(X0,sK5(X0,X3),sK4(X0))
                  & r1_orders_2(X0,sK5(X0,X3),sK3(X0))
                  & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,sK4(X0))
                | ~ r1_orders_2(X0,X3,sK3(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
                        | ~ r1_orders_2(X0,X8,X6)
                        | ~ r1_orders_2(X0,X8,X5)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,sK6(X0,X5,X6),X6)
                    & r1_orders_2(X0,sK6(X0,X5,X6),X5)
                    & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f48,f52,f51,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r1_orders_2(X0,X4,sK3(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK3(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r1_orders_2(X0,X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_orders_2(X0,X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK4(X0))
                & r1_orders_2(X0,X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK4(X0))
            | ~ r1_orders_2(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
        & r1_orders_2(X0,sK5(X0,X3),X2)
        & r1_orders_2(X0,sK5(X0,X3),X1)
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X8,X7)
              | ~ r1_orders_2(X0,X8,X6)
              | ~ r1_orders_2(X0,X8,X5)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK6(X0,X5,X6),X6)
        & r1_orders_2(X0,sK6(X0,X5,X6),X5)
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X8,X7)
                          | ~ r1_orders_2(X0,X8,X6)
                          | ~ r1_orders_2(X0,X8,X5)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X7,X6)
                      & r1_orders_2(X0,X7,X5)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t21_yellow_0.p',d11_lattice3)).

fof(f508,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f507,f69])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f507,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ r1_orders_2(X4,sK6(X4,X5,X3),X3)
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f502,f68])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f502,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ r1_orders_2(X4,sK6(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,sK6(X4,X5,X3),X3)
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ r1_orders_2(X4,sK6(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,sK6(X4,X5,X3),X3)
      | ~ m1_subset_1(sK6(X4,X5,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f338,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X5,X2)
                                & r1_orders_2(X0,X5,X1) )
                             => r1_orders_2(X0,X5,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t21_yellow_0.p',t19_yellow_0)).

fof(f338,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ v2_lattice3(X10) ) ),
    inference(subsumption_resolution,[],[f337,f67])).

fof(f337,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v2_lattice3(X10)
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f336,f69])).

fof(f336,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v2_lattice3(X10)
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X11)
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f323,f68])).

fof(f323,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X9)
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ v2_lattice3(X10)
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X11)
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f318])).

fof(f318,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X9)
      | ~ m1_subset_1(sK7(X10,X11,X9,sK6(X10,X9,X11)),u1_struct_0(X10))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ v2_lattice3(X10)
      | r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X9)
      | ~ r1_orders_2(X10,sK6(X10,X9,X11),X11)
      | ~ m1_subset_1(sK6(X10,X9,X11),u1_struct_0(X10))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10) ) ),
    inference(resolution,[],[f268,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f268,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK7(X4,X6,X7,sK6(X4,X5,X6)),X5)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,sK6(X4,X5,X6),X7)
      | ~ m1_subset_1(sK7(X4,X6,X7,sK6(X4,X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f267,f67])).

fof(f267,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,sK7(X4,X6,X7,sK6(X4,X5,X6)),X5)
      | ~ m1_subset_1(sK7(X4,X6,X7,sK6(X4,X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f263,f69])).

fof(f263,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,X5,X6),X7)
      | ~ r1_orders_2(X4,sK6(X4,X5,X6),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,sK7(X4,X6,X7,sK6(X4,X5,X6)),X5)
      | ~ m1_subset_1(sK7(X4,X6,X7,sK6(X4,X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,X5,X6),X7)
      | ~ r1_orders_2(X4,sK6(X4,X5,X6),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,sK7(X4,X6,X7,sK6(X4,X5,X6)),X5)
      | ~ m1_subset_1(sK7(X4,X6,X7,sK6(X4,X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v2_lattice3(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,sK6(X4,X5,X6),X7)
      | ~ r1_orders_2(X4,sK6(X4,X5,X6),X6)
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f162,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f162,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6) ) ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f159,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X7)
      | ~ m1_subset_1(sK6(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9,X10),X7)
      | ~ m1_subset_1(sK6(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X10)
      | ~ r1_orders_2(X6,sK7(X6,X7,X8,sK6(X6,X9,X10)),X9)
      | ~ m1_subset_1(sK7(X6,X7,X8,sK6(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v2_lattice3(X6)
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl10_3
  <=> ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f10283,plain,
    ( spl10_1
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f10282])).

fof(f10282,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f10281,f61])).

fof(f10281,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f10280,f102])).

fof(f102,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl10_1
  <=> ~ v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f10280,plain,
    ( v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_13 ),
    inference(resolution,[],[f10049,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10049,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f10048])).

fof(f10048,plain,
    ( spl10_13
  <=> ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f10130,plain,
    ( spl10_1
    | spl10_11 ),
    inference(avatar_contradiction_clause,[],[f10129])).

fof(f10129,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f10128,f61])).

fof(f10128,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f10127,f102])).

fof(f10127,plain,
    ( v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_11 ),
    inference(resolution,[],[f10046,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10046,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f10045])).

fof(f10045,plain,
    ( spl10_11
  <=> ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f10050,plain,
    ( ~ spl10_11
    | ~ spl10_13
    | spl10_1
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f10043,f119,f101,f10048,f10045])).

fof(f119,plain,
    ( spl10_8
  <=> ! [X3,X4] :
        ( r2_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f10043,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f10042,f61])).

fof(f10042,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f10041,f102])).

fof(f10041,plain,
    ( v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f10034,f60])).

fof(f10034,plain,
    ( ~ v5_orders_2(sK0)
    | v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(resolution,[],[f10033,f120])).

fof(f120,plain,
    ( ! [X4,X3] :
        ( r2_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f10033,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f10032,f71])).

fof(f10032,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f10031,f72])).

fof(f10031,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f10030,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t21_yellow_0.p',dt_k11_lattice3)).

fof(f10030,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(k11_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f10029,f1844])).

fof(f1844,plain,(
    ! [X21,X19,X20] :
      ( r1_orders_2(X19,k11_lattice3(X19,X21,X20),X20)
      | ~ r2_yellow_0(X19,k2_tarski(X20,X21))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19) ) ),
    inference(duplicate_literal_removal,[],[f1741])).

fof(f1741,plain,(
    ! [X21,X19,X20] :
      ( r1_orders_2(X19,k11_lattice3(X19,X21,X20),X20)
      | ~ r2_yellow_0(X19,k2_tarski(X20,X21))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ r2_yellow_0(X19,k2_tarski(X20,X21)) ) ),
    inference(superposition,[],[f151,f1474])).

fof(f1474,plain,(
    ! [X6,X8,X7] :
      ( k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ r2_yellow_0(X6,k2_tarski(X7,X8)) ) ),
    inference(subsumption_resolution,[],[f1473,f95])).

fof(f1473,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ m1_subset_1(k11_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f1472,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
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
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1472,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X8)
      | ~ m1_subset_1(k11_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f1467,f151])).

fof(f1467,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X8)
      | ~ m1_subset_1(k11_lattice3(X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(duplicate_literal_removal,[],[f1448])).

fof(f1448,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_yellow_0(X6,k2_tarski(X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | k11_lattice3(X6,X7,X8) = k11_lattice3(X6,X8,X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X7)
      | ~ r1_orders_2(X6,k11_lattice3(X6,X7,X8),X8)
      | ~ m1_subset_1(k11_lattice3(X6,X7,X8),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(resolution,[],[f527,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f527,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X2,X3,k11_lattice3(X0,X1,X2)),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f526,f95])).

fof(f526,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f525,f149])).

fof(f525,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f510])).

fof(f510,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK7(X0,X2,X3,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X3)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f240,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f240,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X7)
      | ~ r2_yellow_0(X3,k2_tarski(X6,X7))
      | ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k11_lattice3(X3,X4,X5) = k11_lattice3(X3,X6,X7)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f239,f95])).

fof(f239,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X6)
      | ~ r2_yellow_0(X3,k2_tarski(X6,X7))
      | ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k11_lattice3(X3,X4,X5) = k11_lattice3(X3,X6,X7)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X6,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f235,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f235,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X6)
      | ~ m1_subset_1(sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),u1_struct_0(X3))
      | ~ r2_yellow_0(X3,k2_tarski(X6,X7))
      | ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k11_lattice3(X3,X4,X5) = k11_lattice3(X3,X6,X7)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X6,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X6)
      | ~ m1_subset_1(sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),u1_struct_0(X3))
      | ~ r2_yellow_0(X3,k2_tarski(X6,X7))
      | ~ r1_orders_2(X3,sK7(X3,X4,X5,k11_lattice3(X3,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k11_lattice3(X3,X4,X5) = k11_lattice3(X3,X6,X7)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X6,X7),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X6,X7),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f183,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f97,f95])).

fof(f97,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
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
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10029,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ r1_orders_2(X0,k11_lattice3(X0,sK4(X0),sK3(X0)),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f9992])).

fof(f9992,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ r1_orders_2(X0,k11_lattice3(X0,sK4(X0),sK3(X0)),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,sK4(X0),sK3(X0)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(sK3(X0),sK4(X0)))
      | ~ m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f1678,f1845])).

fof(f1845,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,k11_lattice3(X16,X18,X17),X18)
      | ~ r2_yellow_0(X16,k2_tarski(X17,X18))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16) ) ),
    inference(duplicate_literal_removal,[],[f1740])).

fof(f1740,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,k11_lattice3(X16,X18,X17),X18)
      | ~ r2_yellow_0(X16,k2_tarski(X17,X18))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ r2_yellow_0(X16,k2_tarski(X17,X18)) ) ),
    inference(superposition,[],[f149,f1474])).

fof(f1678,plain,(
    ! [X1] :
      ( ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK4(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1)
      | ~ r2_yellow_0(X1,k2_tarski(sK3(X1),sK4(X1)))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK3(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(forward_demodulation,[],[f1677,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t21_yellow_0.p',commutativity_k2_tarski)).

fof(f1677,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK4(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK3(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1674,f72])).

fof(f1674,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ m1_subset_1(sK4(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK4(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK3(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1653])).

fof(f1653,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK4(X1),sK3(X1)))
      | ~ m1_subset_1(sK4(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_lattice3(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK4(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK3(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1))
      | v2_lattice3(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK4(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK4(X1),sK3(X1)),sK3(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK4(X1),sK3(X1)),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f391,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK5(X0,X3),sK4(X0))
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f391,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,sK3(X0))),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f390,f71])).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,sK3(X0))),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,k2_tarski(X1,sK3(X0)))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,sK3(X0))),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK3(X0))
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK3(X0)),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK3(X0)),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f238,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK5(X0,X3),sK3(X0))
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK3(X0)) ) ),
    inference(subsumption_resolution,[],[f237,f95])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f236,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(sK5(X0,k11_lattice3(X0,X1,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X1)
      | ~ m1_subset_1(sK5(X0,k11_lattice3(X0,X1,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK5(X0,k11_lattice3(X0,X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK4(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,X2),sK3(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f183,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,
    ( spl10_0
    | spl10_8 ),
    inference(avatar_split_clause,[],[f62,f119,f116])).

fof(f62,plain,(
    ! [X4,X3] :
      ( r2_yellow_0(sK0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_lattice3(sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,
    ( ~ spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f63,f112,f101])).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f64,f108,f101])).

fof(f64,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f65,f104,f101])).

fof(f65,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
