%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1543+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:03 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  124 (1043 expanded)
%              Number of leaves         :   16 ( 383 expanded)
%              Depth                    :   42
%              Number of atoms          :  903 (11271 expanded)
%              Number of equality atoms :   19 ( 187 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(subsumption_resolution,[],[f492,f42])).

fof(f42,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        & m1_subset_1(sK5,u1_struct_0(sK3))
        & m1_subset_1(sK4,u1_struct_0(sK3)) )
      | ~ v2_lattice3(sK3) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r2_yellow_0(sK3,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
      | v2_lattice3(sK3) )
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,
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
                ( ~ r2_yellow_0(sK3,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK3)) )
            & m1_subset_1(X1,u1_struct_0(sK3)) )
        | ~ v2_lattice3(sK3) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(sK3,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
        | v2_lattice3(sK3) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_yellow_0(sK3,k2_tarski(X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ~ r2_yellow_0(sK3,k2_tarski(sK4,X2))
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r2_yellow_0(sK3,k2_tarski(sK4,X2))
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v2_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f492,plain,(
    ~ l1_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f491,f351])).

fof(f351,plain,(
    v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f350,f42])).

fof(f350,plain,
    ( v2_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,
    ( v2_lattice3(sK3)
    | v2_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f348,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP0(X0)
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
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f348,plain,
    ( sP0(sK3)
    | v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f347,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,sK8(X0,X3),X3)
                & r1_orders_2(X0,sK8(X0,X3),sK7(X0))
                & r1_orders_2(X0,sK8(X0,X3),sK6(X0))
                & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,sK7(X0))
              | ~ r1_orders_2(X0,X3,sK6(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK7(X0),u1_struct_0(X0))
          & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,X8,sK9(X0,X5,X6))
                      | ~ r1_orders_2(X0,X8,X6)
                      | ~ r1_orders_2(X0,X8,X5)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,sK9(X0,X5,X6),X6)
                  & r1_orders_2(X0,sK9(X0,X5,X6),X5)
                  & m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f30,f34,f33,f32,f31])).

fof(f31,plain,(
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
                    & r1_orders_2(X0,X4,sK6(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK6(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r1_orders_2(X0,X4,sK6(X0))
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_orders_2(X0,X3,sK6(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK7(X0))
                & r1_orders_2(X0,X4,sK6(X0))
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK7(X0))
            | ~ r1_orders_2(X0,X3,sK6(X0))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,sK7(X0))
          & r1_orders_2(X0,X4,sK6(X0))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X3),X3)
        & r1_orders_2(X0,sK8(X0,X3),sK7(X0))
        & r1_orders_2(X0,sK8(X0,X3),sK6(X0))
        & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
            ( r1_orders_2(X0,X8,sK9(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK9(X0,X5,X6),X6)
        & r1_orders_2(X0,sK9(X0,X5,X6),X5)
        & m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f347,plain,
    ( sP0(sK3)
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f346,f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f346,plain,
    ( sP0(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f345,f41])).

fof(f41,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f345,plain,
    ( ~ v5_orders_2(sK3)
    | sP0(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f340,f42])).

fof(f340,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | sP0(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v2_lattice3(sK3) ),
    inference(resolution,[],[f339,f43])).

fof(f43,plain,(
    ! [X4,X3] :
      ( r2_yellow_0(sK3,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | v2_lattice3(sK3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0))) ) ),
    inference(forward_demodulation,[],[f337,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f337,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0))) ) ),
    inference(subsumption_resolution,[],[f336,f54])).

fof(f336,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0)))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f335,f53])).

fof(f335,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f334,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f334,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ m1_subset_1(k11_lattice3(X0,sK7(X0),sK6(X0)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f333,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
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
    inference(definition_folding,[],[f13,f19])).

fof(f19,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_0)).

fof(f333,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r1_orders_2(X0,k11_lattice3(X0,sK7(X0),sK6(X0)),sK6(X0))
      | ~ m1_subset_1(k11_lattice3(X0,sK7(X0),sK6(X0)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r2_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r1_orders_2(X0,k11_lattice3(X0,sK7(X0),sK6(X0)),sK6(X0))
      | ~ m1_subset_1(k11_lattice3(X0,sK7(X0),sK6(X0)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(sK7(X0),sK6(X0)))
      | ~ m1_subset_1(k11_lattice3(X0,sK7(X0),sK6(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f312,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f312,plain,(
    ! [X1] :
      ( ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK7(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r2_yellow_0(X1,k2_tarski(sK6(X1),sK7(X1)))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK6(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK7(X1),sK6(X1)),u1_struct_0(X1)) ) ),
    inference(forward_demodulation,[],[f311,f72])).

fof(f311,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK7(X1),sK6(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK7(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK6(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK7(X1),sK6(X1)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f308,f54])).

fof(f308,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK7(X1),sK6(X1)))
      | ~ m1_subset_1(sK7(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK7(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK6(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK7(X1),sK6(X1)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(sK7(X1),sK6(X1)))
      | ~ m1_subset_1(sK7(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK7(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK6(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK7(X1),sK6(X1)),u1_struct_0(X1))
      | sP0(X1)
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK7(X1))
      | ~ r1_orders_2(X1,k11_lattice3(X1,sK7(X1),sK6(X1)),sK6(X1))
      | ~ m1_subset_1(k11_lattice3(X1,sK7(X1),sK6(X1)),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f227,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK8(X0,X3),sK7(X0))
      | sP0(X0)
      | ~ r1_orders_2(X0,X3,sK7(X0))
      | ~ r1_orders_2(X0,X3,sK6(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,k11_lattice3(X0,X1,sK6(X0))),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,sK6(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK7(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK6(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK6(X0)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f226,f53])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,k11_lattice3(X0,X1,sK6(X0))),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,sK6(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK7(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK6(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK6(X0)),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,k11_lattice3(X0,X1,sK6(X0))),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,sK6(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK7(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK6(X0))
      | sP0(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK7(X0))
      | ~ r1_orders_2(X0,k11_lattice3(X0,X1,sK6(X0)),sK6(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,sK6(X0)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f211,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK8(X0,X3),sK6(X0))
      | sP0(X0)
      | ~ r1_orders_2(X0,X3,sK7(X0))
      | ~ r1_orders_2(X0,X3,sK6(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f211,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X5)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK7(X4))
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK6(X4)) ) ),
    inference(subsumption_resolution,[],[f210,f73])).

fof(f210,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X5)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK7(X4))
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK6(X4)) ) ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK8(X0,X3),u1_struct_0(X0))
      | sP0(X0)
      | ~ r1_orders_2(X0,X3,sK7(X0))
      | ~ r1_orders_2(X0,X3,sK6(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f205,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X5)
      | ~ m1_subset_1(sK8(X4,k11_lattice3(X4,X5,X6)),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK7(X4))
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK6(X4)) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,k11_lattice3(X4,X5,X6)),X5)
      | ~ m1_subset_1(sK8(X4,k11_lattice3(X4,X5,X6)),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK7(X4))
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),sK6(X4))
      | ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,sK8(X0,X3),X3)
      | sP0(X0)
      | ~ r1_orders_2(X0,X3,sK7(X0))
      | ~ r1_orders_2(X0,X3,sK6(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X4,X2)
      | ~ r1_orders_2(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_orders_2(X0,X4,X2)
      | ~ r1_orders_2(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f491,plain,
    ( ~ v2_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f489,f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f47,f59])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_lattice3(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f489,plain,(
    ~ sP0(sK3) ),
    inference(subsumption_resolution,[],[f488,f351])).

fof(f488,plain,
    ( ~ sP0(sK3)
    | ~ v2_lattice3(sK3) ),
    inference(resolution,[],[f487,f44])).

fof(f44,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f487,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0(sK3) ),
    inference(subsumption_resolution,[],[f486,f351])).

fof(f486,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3) ),
    inference(resolution,[],[f485,f45])).

fof(f45,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f485,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ sP0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f484,f351])).

fof(f484,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f483,f41])).

fof(f483,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f478,f42])).

fof(f478,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v2_lattice3(sK3) ),
    inference(resolution,[],[f477,f46])).

fof(f46,plain,
    ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f477,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ sP0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f476,f49])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f476,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP0(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP0(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f442,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f442,plain,(
    ! [X10,X11,X9] :
      ( ~ sP2(X11,X9,X10,sK9(X10,X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r2_yellow_0(X10,k2_tarski(X9,X11))
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f441,f51])).

fof(f51,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK9(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f441,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r2_yellow_0(X10,k2_tarski(X9,X11))
      | ~ sP2(X11,X9,X10,sK9(X10,X11,X9))
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X9) ) ),
    inference(subsumption_resolution,[],[f433,f50])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK9(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f433,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r2_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X11)
      | ~ sP2(X11,X9,X10,sK9(X10,X11,X9))
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X9) ) ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r2_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X11)
      | ~ sP2(X11,X9,X10,sK9(X10,X11,X9))
      | r2_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X11)
      | ~ r1_orders_2(X10,sK9(X10,X11,X9),X9)
      | ~ sP2(X11,X9,X10,sK9(X10,X11,X9)) ) ),
    inference(resolution,[],[f414,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,sK10(X0,X1,X2,X3),X0)
      | r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,sK10(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK10(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK10(X0,X1,X2,X3),X1)
        & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,sK10(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK10(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK10(X0,X1,X2,X3),X1)
        & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f414,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X5,X6,X4,sK9(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X5))
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X5)
      | ~ sP2(X5,X6,X4,sK9(X4,X7,X6)) ) ),
    inference(subsumption_resolution,[],[f411,f51])).

fof(f411,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X5,X6,X4,sK9(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X5))
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X5)
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X6)
      | ~ sP2(X5,X6,X4,sK9(X4,X7,X6)) ) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X5,X6,X4,sK9(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r2_yellow_0(X4,k2_tarski(X6,X5))
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X5)
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X6)
      | ~ sP2(X5,X6,X4,sK9(X4,X7,X6))
      | r2_yellow_0(X4,k2_tarski(X6,X5))
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X5)
      | ~ r1_orders_2(X4,sK9(X4,X7,X6),X6)
      | ~ sP2(X5,X6,X4,sK9(X4,X7,X6)) ) ),
    inference(resolution,[],[f132,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,sK10(X0,X1,X2,X3),X1)
      | r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK10(X9,X10,X8,sK9(X8,X11,X12)),X12)
      | ~ r1_orders_2(X8,sK10(X9,X10,X8,sK9(X8,X11,X12)),X11)
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ sP0(X8)
      | r2_yellow_0(X8,k2_tarski(X10,X9))
      | ~ r1_orders_2(X8,sK9(X8,X11,X12),X9)
      | ~ r1_orders_2(X8,sK9(X8,X11,X12),X10)
      | ~ sP2(X9,X10,X8,sK9(X8,X11,X12)) ) ),
    inference(subsumption_resolution,[],[f130,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2))
      | r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f130,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK10(X9,X10,X8,sK9(X8,X11,X12)),X12)
      | ~ r1_orders_2(X8,sK10(X9,X10,X8,sK9(X8,X11,X12)),X11)
      | ~ m1_subset_1(sK10(X9,X10,X8,sK9(X8,X11,X12)),u1_struct_0(X8))
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ sP0(X8)
      | r2_yellow_0(X8,k2_tarski(X10,X9))
      | ~ r1_orders_2(X8,sK9(X8,X11,X12),X9)
      | ~ r1_orders_2(X8,sK9(X8,X11,X12),X10)
      | ~ sP2(X9,X10,X8,sK9(X8,X11,X12)) ) ),
    inference(resolution,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X2,sK10(X0,X1,X2,X3),X3)
      | r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK9(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
