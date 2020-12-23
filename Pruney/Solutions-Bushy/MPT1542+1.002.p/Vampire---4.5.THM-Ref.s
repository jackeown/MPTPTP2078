%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1542+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (1015 expanded)
%              Number of leaves         :   15 ( 375 expanded)
%              Depth                    :   39
%              Number of atoms          :  880 (11171 expanded)
%              Number of equality atoms :   17 ( 171 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(subsumption_resolution,[],[f539,f41])).

fof(f41,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( ~ r1_yellow_0(sK3,k2_tarski(sK4,sK5))
        & m1_subset_1(sK5,u1_struct_0(sK3))
        & m1_subset_1(sK4,u1_struct_0(sK3)) )
      | ~ v1_lattice3(sK3) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r1_yellow_0(sK3,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
      | v1_lattice3(sK3) )
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,
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
                ( ~ r1_yellow_0(sK3,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK3)) )
            & m1_subset_1(X1,u1_struct_0(sK3)) )
        | ~ v1_lattice3(sK3) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(sK3,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
        | v1_lattice3(sK3) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_yellow_0(sK3,k2_tarski(X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ~ r1_yellow_0(sK3,k2_tarski(sK4,X2))
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_yellow_0(sK3,k2_tarski(sK4,X2))
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ~ r1_yellow_0(sK3,k2_tarski(sK4,sK5))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v1_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

fof(f539,plain,(
    ~ l1_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f538,f378])).

fof(f378,plain,(
    v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f377,f41])).

fof(f377,plain,
    ( v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,
    ( v1_lattice3(sK3)
    | v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f375,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP0(X0)
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
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f375,plain,
    ( sP0(sK3)
    | v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f374,f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ( ~ r1_orders_2(X0,X3,sK8(X0,X3))
                & r1_orders_2(X0,sK7(X0),sK8(X0,X3))
                & r1_orders_2(X0,sK6(X0),sK8(X0,X3))
                & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK7(X0),X3)
              | ~ r1_orders_2(X0,sK6(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK7(X0),u1_struct_0(X0))
          & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( ! [X8] :
                      ( r1_orders_2(X0,sK9(X0,X5,X6),X8)
                      | ~ r1_orders_2(X0,X6,X8)
                      | ~ r1_orders_2(X0,X5,X8)
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X6,sK9(X0,X5,X6))
                  & r1_orders_2(X0,X5,sK9(X0,X5,X6))
                  & m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f29,f33,f32,f31,f30])).

fof(f30,plain,(
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
                    & r1_orders_2(X0,sK6(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK6(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,sK6(X0),X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,sK6(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK7(X0),X4)
                & r1_orders_2(X0,sK6(X0),X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK7(X0),X3)
            | ~ r1_orders_2(X0,sK6(X0),X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,sK7(X0),X4)
          & r1_orders_2(X0,sK6(X0),X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK8(X0,X3))
        & r1_orders_2(X0,sK7(X0),sK8(X0,X3))
        & r1_orders_2(X0,sK6(X0),sK8(X0,X3))
        & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
            ( r1_orders_2(X0,sK9(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK9(X0,X5,X6))
        & r1_orders_2(X0,X5,sK9(X0,X5,X6))
        & m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f374,plain,
    ( sP0(sK3)
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f373,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f373,plain,
    ( sP0(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f372,f41])).

fof(f372,plain,
    ( sP0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f367,f40])).

fof(f40,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f367,plain,
    ( ~ v5_orders_2(sK3)
    | sP0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK7(sK3),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6(sK3),u1_struct_0(sK3))
    | v1_lattice3(sK3) ),
    inference(resolution,[],[f366,f42])).

fof(f42,plain,(
    ! [X4,X3] :
      ( r1_yellow_0(sK3,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | v1_lattice3(sK3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f366,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f365,f52])).

fof(f365,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f364,f53])).

fof(f364,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f363,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f363,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),sK7(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f362,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP2(X2,X1,X0,X3)
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
    inference(definition_folding,[],[f12,f18])).

fof(f18,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f362,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),sK7(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),sK7(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),sK7(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),sK7(X0)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),sK7(X0)))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),sK7(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f342,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f342,plain,(
    ! [X1] :
      ( ~ r1_orders_2(X1,sK7(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_yellow_0(X1,k2_tarski(sK6(X1),sK7(X1)))
      | ~ r1_orders_2(X1,sK6(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK6(X1),sK7(X1)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f339,f53])).

fof(f339,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(X1,k2_tarski(sK6(X1),sK7(X1)))
      | ~ m1_subset_1(sK7(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_orders_2(X1,sK7(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ r1_orders_2(X1,sK6(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK6(X1),sK7(X1)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(X1,k2_tarski(sK6(X1),sK7(X1)))
      | ~ m1_subset_1(sK7(X1),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | sP0(X1)
      | ~ r1_orders_2(X1,sK7(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ r1_orders_2(X1,sK6(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK6(X1),sK7(X1)),u1_struct_0(X1))
      | sP0(X1)
      | ~ r1_orders_2(X1,sK7(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ r1_orders_2(X1,sK6(X1),k10_lattice3(X1,sK6(X1),sK7(X1)))
      | ~ m1_subset_1(k10_lattice3(X1,sK6(X1),sK7(X1)),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f287,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK7(X0),sK8(X0,X3))
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),X3)
      | ~ r1_orders_2(X0,sK6(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,sK6(X0),X1)))
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f286,f52])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,sK6(X0),X1)))
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,sK6(X0),X1)))
      | ~ r1_yellow_0(X0,k2_tarski(sK6(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),X1))
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,sK6(X0),X1))
      | ~ m1_subset_1(k10_lattice3(X0,sK6(X0),X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f178,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK6(X0),sK8(X0,X3))
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),X3)
      | ~ r1_orders_2(X0,sK6(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f177,f71])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_orders_2(X0,X2,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,X2,X1)) ) ),
    inference(subsumption_resolution,[],[f176,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK8(X0,X3),u1_struct_0(X0))
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),X3)
      | ~ r1_orders_2(X0,sK6(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_orders_2(X0,X2,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ m1_subset_1(sK8(X0,k10_lattice3(X0,X2,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,X2,X1)) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ r1_orders_2(X0,X2,sK8(X0,k10_lattice3(X0,X2,X1)))
      | ~ m1_subset_1(sK8(X0,k10_lattice3(X0,X2,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),k10_lattice3(X0,X2,X1))
      | ~ r1_orders_2(X0,sK6(X0),k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,X3,sK8(X0,X3))
      | sP0(X0)
      | ~ r1_orders_2(X0,sK7(X0),X3)
      | ~ r1_orders_2(X0,sK6(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f538,plain,
    ( ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f536,f76])).

fof(f76,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f46,f58])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v1_lattice3(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f536,plain,(
    ~ sP0(sK3) ),
    inference(subsumption_resolution,[],[f535,f378])).

fof(f535,plain,
    ( ~ sP0(sK3)
    | ~ v1_lattice3(sK3) ),
    inference(resolution,[],[f534,f43])).

fof(f43,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f534,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0(sK3) ),
    inference(subsumption_resolution,[],[f533,f378])).

fof(f533,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0(sK3)
    | ~ v1_lattice3(sK3) ),
    inference(resolution,[],[f532,f44])).

fof(f44,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f532,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP0(sK3) ),
    inference(subsumption_resolution,[],[f531,f378])).

fof(f531,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f530,f40])).

fof(f530,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3) ),
    inference(subsumption_resolution,[],[f525,f41])).

fof(f525,plain,
    ( ~ sP0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v1_lattice3(sK3) ),
    inference(resolution,[],[f497,f45])).

fof(f45,plain,
    ( ~ r1_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f497,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,k2_tarski(X0,X2))
      | ~ sP0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f496,f48])).

fof(f48,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK9(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP0(X1)
      | r1_yellow_0(X1,k2_tarski(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP0(X1)
      | r1_yellow_0(X1,k2_tarski(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(sK9(X1,X0,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f488,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f488,plain,(
    ! [X10,X11,X9] :
      ( ~ sP2(X9,X11,X10,sK9(X10,X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f487,f49])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK9(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f487,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ sP2(X9,X11,X10,sK9(X10,X11,X9))
      | ~ r1_orders_2(X10,X11,sK9(X10,X11,X9)) ) ),
    inference(subsumption_resolution,[],[f479,f50])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK9(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f479,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK9(X10,X11,X9))
      | ~ sP2(X9,X11,X10,sK9(X10,X11,X9))
      | ~ r1_orders_2(X10,X11,sK9(X10,X11,X9)) ) ),
    inference(duplicate_literal_removal,[],[f470])).

fof(f470,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ sP0(X10)
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK9(X10,X11,X9))
      | ~ sP2(X9,X11,X10,sK9(X10,X11,X9))
      | r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ r1_orders_2(X10,X9,sK9(X10,X11,X9))
      | ~ r1_orders_2(X10,X11,sK9(X10,X11,X9))
      | ~ sP2(X9,X11,X10,sK9(X10,X11,X9)) ) ),
    inference(resolution,[],[f460,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,X0,sK10(X0,X1,X2,X3))
      | r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,X3,sK10(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK10(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK10(X0,X1,X2,X3))
        & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,X3,sK10(X0,X1,X2,X3))
        & r1_orders_2(X2,X0,sK10(X0,X1,X2,X3))
        & r1_orders_2(X2,X1,sK10(X0,X1,X2,X3))
        & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_yellow_0(X2,k2_tarski(X1,X0))
        & k10_lattice3(X2,X1,X0) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X2,X3,X4)
          & r1_orders_2(X2,X0,X4)
          & r1_orders_2(X2,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
        & k10_lattice3(X0,X1,X2) = X3 )
      | ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f460,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK10(X6,X7,X4,sK9(X4,X7,X5)))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X6))
      | ~ r1_orders_2(X4,X6,sK9(X4,X7,X5))
      | ~ sP2(X6,X7,X4,sK9(X4,X7,X5)) ) ),
    inference(subsumption_resolution,[],[f457,f49])).

fof(f457,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK10(X6,X7,X4,sK9(X4,X7,X5)))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X6))
      | ~ r1_orders_2(X4,X6,sK9(X4,X7,X5))
      | ~ r1_orders_2(X4,X7,sK9(X4,X7,X5))
      | ~ sP2(X6,X7,X4,sK9(X4,X7,X5)) ) ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK10(X6,X7,X4,sK9(X4,X7,X5)))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ sP0(X4)
      | r1_yellow_0(X4,k2_tarski(X7,X6))
      | ~ r1_orders_2(X4,X6,sK9(X4,X7,X5))
      | ~ r1_orders_2(X4,X7,sK9(X4,X7,X5))
      | ~ sP2(X6,X7,X4,sK9(X4,X7,X5))
      | r1_yellow_0(X4,k2_tarski(X7,X6))
      | ~ r1_orders_2(X4,X6,sK9(X4,X7,X5))
      | ~ r1_orders_2(X4,X7,sK9(X4,X7,X5))
      | ~ sP2(X6,X7,X4,sK9(X4,X7,X5)) ) ),
    inference(resolution,[],[f124,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,X1,sK10(X0,X1,X2,X3))
      | r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,X12,sK10(X10,X11,X8,sK9(X8,X12,X9)))
      | ~ r1_orders_2(X8,X9,sK10(X10,X11,X8,sK9(X8,X12,X9)))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ sP0(X8)
      | r1_yellow_0(X8,k2_tarski(X11,X10))
      | ~ r1_orders_2(X8,X10,sK9(X8,X12,X9))
      | ~ r1_orders_2(X8,X11,sK9(X8,X12,X9))
      | ~ sP2(X10,X11,X8,sK9(X8,X12,X9)) ) ),
    inference(subsumption_resolution,[],[f122,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X2))
      | r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,X9,sK10(X10,X11,X8,sK9(X8,X12,X9)))
      | ~ r1_orders_2(X8,X12,sK10(X10,X11,X8,sK9(X8,X12,X9)))
      | ~ m1_subset_1(sK10(X10,X11,X8,sK9(X8,X12,X9)),u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ sP0(X8)
      | r1_yellow_0(X8,k2_tarski(X11,X10))
      | ~ r1_orders_2(X8,X10,sK9(X8,X12,X9))
      | ~ r1_orders_2(X8,X11,sK9(X8,X12,X9))
      | ~ sP2(X10,X11,X8,sK9(X8,X12,X9)) ) ),
    inference(resolution,[],[f51,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X2,X3,sK10(X0,X1,X2,X3))
      | r1_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,X0,X3)
      | ~ r1_orders_2(X2,X1,X3)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK9(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

%------------------------------------------------------------------------------
