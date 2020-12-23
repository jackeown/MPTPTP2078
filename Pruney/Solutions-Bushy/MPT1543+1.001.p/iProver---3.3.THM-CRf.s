%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1543+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:50 EST 2020

% Result     : Theorem 11.13s
% Output     : CNFRefutation 11.13s
% Verified   : 
% Statistics : Number of formulae       :  278 (14329 expanded)
%              Number of clauses        :  206 (3652 expanded)
%              Number of leaves         :   19 (3563 expanded)
%              Depth                    :   46
%              Number of atoms          : 1702 (114373 expanded)
%              Number of equality atoms :  240 (4861 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f14,plain,(
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

fof(f15,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(X1,sK10))
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK9,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
                ( ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK8)) )
            & m1_subset_1(X1,u1_struct_0(sK8)) )
        | ~ v2_lattice3(sK8) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(sK8,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
        | v2_lattice3(sK8) )
      & l1_orders_2(sK8)
      & v5_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
        & m1_subset_1(sK10,u1_struct_0(sK8))
        & m1_subset_1(sK9,u1_struct_0(sK8)) )
      | ~ v2_lattice3(sK8) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r2_yellow_0(sK8,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK8)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK8)) )
      | v2_lattice3(sK8) )
    & l1_orders_2(sK8)
    & v5_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f36,f39,f38,f37])).

fof(f70,plain,(
    ! [X4,X3] :
      ( r2_yellow_0(sK8,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK8))
      | ~ m1_subset_1(X3,u1_struct_0(sK8))
      | v2_lattice3(sK8) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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

fof(f18,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f17,f16])).

fof(f54,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_lattice3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_lattice3(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f27,f26,f25,f24])).

fof(f49,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f33])).

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
    inference(equality_resolution,[],[f66])).

fof(f68,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X2,X4,X3)
          & r1_orders_2(X2,X4,X0)
          & r1_orders_2(X2,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_yellow_0(X2,k2_tarski(X1,X0))
        & k11_lattice3(X2,X1,X0) = X3 )
      | ( ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
        & r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) )
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X2,X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X2,X1,X0) = X3
      | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f48,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK4(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK3(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0,X3] :
      ( sP0(X0)
      | ~ r1_orders_2(X0,sK5(X0,X3),X3)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X2,k2_tarski(X1,X0))
      | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X2,X3,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7082,plain,
    ( k2_tarski(X0_49,X1_49) = k2_tarski(X2_49,X3_49)
    | X0_49 != X2_49
    | X1_49 != X3_49 ),
    theory(equality)).

cnf(c_7085,plain,
    ( ~ r2_yellow_0(X0_48,X0_50)
    | r2_yellow_0(X0_48,X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_9053,plain,
    ( ~ r2_yellow_0(X0_48,k2_tarski(X0_49,X1_49))
    | r2_yellow_0(X0_48,k2_tarski(X2_49,X3_49))
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    inference(resolution,[status(thm)],[c_7082,c_7085])).

cnf(c_30,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | sP1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_353,plain,
    ( ~ l1_orders_2(X0)
    | sP0(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_535,plain,
    ( sP0(X0)
    | ~ v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_31])).

cnf(c_536,plain,
    ( sP0(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_2767,plain,
    ( sP0(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_536])).

cnf(c_2822,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_30,c_2767])).

cnf(c_7058,negated_conjecture,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2822])).

cnf(c_12123,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | sP0(sK8)
    | X0_49 != X2_49
    | X1_49 != X3_49 ),
    inference(resolution,[status(thm)],[c_9053,c_7058])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k11_lattice3(X1,X0,X2),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_7065,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_546])).

cnf(c_7580,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7065])).

cnf(c_7,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7071,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_7574,plain,
    ( m1_subset_1(sK4(X0_48),u1_struct_0(X0_48)) = iProver_top
    | sP0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7071])).

cnf(c_7587,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7058])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_439,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
    | ~ r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_440,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_31])).

cnf(c_445,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X1,X2),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_571,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,X0,k11_lattice3(sK8,X1,X2))
    | ~ r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_445])).

cnf(c_7062,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,X0_49,k11_lattice3(sK8,X1_49,X2_49))
    | ~ r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_7583,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,X0_49,k11_lattice3(sK8,X1_49,X2_49)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7062])).

cnf(c_26,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_389,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_390,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_31])).

cnf(c_395,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_570,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X0)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_395])).

cnf(c_7063,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_7582,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7063])).

cnf(c_21,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_475,plain,
    ( sP2(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_476,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | sP2(X0,X1,sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_31])).

cnf(c_481,plain,
    ( sP2(X0,X1,sK8,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_725,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X3)
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_481])).

cnf(c_726,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_7056,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X1_49)
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_49,X2_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_726])).

cnf(c_7589,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,sK7(X1_49,X0_49,sK8,X2_49),X0_49) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7056])).

cnf(c_19,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
    | k11_lattice3(X2,X1,X0) = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_777,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X2,X3,X0,X1),X1)
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | k11_lattice3(X0,X3,X2) = X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_481])).

cnf(c_778,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_7054,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | ~ r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49)
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | k11_lattice3(sK8,X1_49,X2_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_778])).

cnf(c_7591,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X2_49
    | r1_orders_2(sK8,X2_49,X0_49) != iProver_top
    | r1_orders_2(sK8,X2_49,X1_49) != iProver_top
    | r1_orders_2(sK8,sK7(X1_49,X0_49,sK8,X2_49),X2_49) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7054])).

cnf(c_8556,plain,
    ( k11_lattice3(sK8,X0_49,X1_49) = X0_49
    | r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X0_49) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7589,c_7591])).

cnf(c_9255,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7582,c_8556])).

cnf(c_7118,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7065])).

cnf(c_10000,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9255,c_7118])).

cnf(c_10001,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),k11_lattice3(sK8,X0_49,X1_49)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10000])).

cnf(c_10011,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7583,c_10001])).

cnf(c_25,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_416,plain,
    ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_417,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_31])).

cnf(c_420,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_569,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0,X1),X1)
    | ~ r2_yellow_0(sK8,k2_tarski(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_546,c_420])).

cnf(c_7064,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_7121,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7064])).

cnf(c_7124,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7063])).

cnf(c_10723,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10011,c_7118,c_7121,c_7124])).

cnf(c_10724,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10723])).

cnf(c_10733,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49) = k11_lattice3(sK8,X0_49,X1_49)
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7587,c_10724])).

cnf(c_10995,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,X0_49,sK4(sK8)),X0_49) = k11_lattice3(sK8,X0_49,sK4(sK8))
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7574,c_10733])).

cnf(c_11339,plain,
    ( k11_lattice3(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),sK4(sK8)),k11_lattice3(sK8,X0_49,X1_49)) = k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),sK4(sK8))
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7580,c_10995])).

cnf(c_8,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_87,plain,
    ( m1_subset_1(sK3(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_89,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_90,plain,
    ( m1_subset_1(sK4(X0),u1_struct_0(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_92,plain,
    ( m1_subset_1(sK4(sK8),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_7985,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7065])).

cnf(c_8208,plain,
    ( m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7985])).

cnf(c_8209,plain,
    ( m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8208])).

cnf(c_7960,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,sK3(sK8)),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7064])).

cnf(c_8219,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7960])).

cnf(c_8220,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8219])).

cnf(c_7961,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,X0_49,sK3(sK8)),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7063])).

cnf(c_8233,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7961])).

cnf(c_8234,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8233])).

cnf(c_7963,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7058])).

cnf(c_8474,plain,
    ( r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7963])).

cnf(c_8475,plain,
    ( r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) = iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8474])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | r1_orders_2(X0,sK5(X0,X1),sK4(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7074,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | r1_orders_2(X0_48,sK5(X0_48,X0_49),sK4(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_8718,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7074])).

cnf(c_9743,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8718])).

cnf(c_9744,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8)) = iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9743])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | r1_orders_2(X0,sK5(X0,X1),sK3(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7073,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | r1_orders_2(X0_48,sK5(X0_48,X0_49),sK3(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_8719,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),sK3(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7073])).

cnf(c_9750,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8719])).

cnf(c_9751,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8)) = iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9750])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7072,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | m1_subset_1(sK5(X0_48,X0_49),u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_8720,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),X0_49),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),X0_49),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),X0_49)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7072])).

cnf(c_9757,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_8720])).

cnf(c_9758,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8)) = iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9757])).

cnf(c_9956,plain,
    ( ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),X0_49)
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,X0_49,sK3(sK8)))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,sK3(sK8)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_7062])).

cnf(c_11610,plain,
    ( r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8)))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_9956])).

cnf(c_11612,plain,
    ( r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8))) = iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),sK4(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11610])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0))
    | ~ r1_orders_2(X0,X1,sK4(X0))
    | ~ r1_orders_2(X0,sK5(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7075,plain,
    ( ~ r1_orders_2(X0_48,X0_49,sK3(X0_48))
    | ~ r1_orders_2(X0_48,X0_49,sK4(X0_48))
    | ~ r1_orders_2(X0_48,sK5(X0_48,X0_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_11611,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8))
    | ~ r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8)))
    | ~ m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8))
    | sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7075])).

cnf(c_11614,plain,
    ( r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK3(sK8)) != iProver_top
    | r1_orders_2(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8)),sK4(sK8)) != iProver_top
    | r1_orders_2(sK8,sK5(sK8,k11_lattice3(sK8,sK4(sK8),sK3(sK8))),k11_lattice3(sK8,sK4(sK8),sK3(sK8))) != iProver_top
    | m1_subset_1(k11_lattice3(sK8,sK4(sK8),sK3(sK8)),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11611])).

cnf(c_11669,plain,
    ( sP0(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11339,c_89,c_92,c_8209,c_8220,c_8234,c_8475,c_9744,c_9751,c_9758,c_11612,c_11614])).

cnf(c_11671,plain,
    ( sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11669])).

cnf(c_12143,plain,
    ( sP0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12123,c_11671])).

cnf(c_27,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_367,plain,
    ( ~ l1_orders_2(X0)
    | ~ sP0(X0)
    | v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_13,c_1])).

cnf(c_525,plain,
    ( ~ sP0(X0)
    | v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_31])).

cnf(c_526,plain,
    ( ~ sP0(sK8)
    | v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_2769,plain,
    ( ~ sP0(sK8)
    | v2_lattice3(sK8) ),
    inference(prop_impl,[status(thm)],[c_526])).

cnf(c_2819,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(bin_hyper_res,[status(thm)],[c_27,c_2769])).

cnf(c_7059,negated_conjecture,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10))
    | ~ sP0(sK8) ),
    inference(subtyping,[status(esa)],[c_2819])).

cnf(c_12221,plain,
    ( ~ r2_yellow_0(sK8,k2_tarski(sK9,sK10)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12143,c_7059])).

cnf(c_7083,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | r1_orders_2(X0_48,X2_49,X3_49)
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    theory(equality)).

cnf(c_7078,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_9154,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | r1_orders_2(X0_48,X2_49,X1_49)
    | X2_49 != X0_49 ),
    inference(resolution,[status(thm)],[c_7083,c_7078])).

cnf(c_9175,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | k11_lattice3(sK8,X0_49,X1_49) = X0_49 ),
    inference(resolution,[status(thm)],[c_7054,c_7056])).

cnf(c_10637,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | r1_orders_2(X0_48,k11_lattice3(sK8,X0_49,X2_49),X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | ~ r1_orders_2(sK8,X0_49,X0_49)
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_9154,c_9175])).

cnf(c_39795,plain,
    ( ~ r1_orders_2(X0_48,k11_lattice3(sK8,X0_49,X1_49),X2_49)
    | r1_orders_2(X0_48,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10637,c_7062])).

cnf(c_7870,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7580])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,X1,sK6(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7069,plain,
    ( ~ r1_orders_2(X0_48,X0_49,X1_49)
    | ~ r1_orders_2(X0_48,X0_49,X2_49)
    | r1_orders_2(X0_48,X0_49,sK6(X0_48,X2_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X2_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_15,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,sK7(X0,X1,X2,X3),X3)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_883,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,sK7(X2,X3,X0,X1),X1)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_481])).

cnf(c_884,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | ~ r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X0)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_7050,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | ~ r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_8890,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_7050,c_7062])).

cnf(c_18,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r2_yellow_0(X2,k2_tarski(X1,X0))
    | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_804,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X3,X0,X1),u1_struct_0(X0))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_481])).

cnf(c_805,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2,X1,sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_7053,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | m1_subset_1(sK7(X2_49,X1_49,sK8,X0_49),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_805])).

cnf(c_10054,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8890,c_7065,c_7053])).

cnf(c_16,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X0)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_858,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X2)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_481])).

cnf(c_859,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X2)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_7051,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X2_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_10089,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10054,c_7051])).

cnf(c_10379,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10089,c_7065,c_7064])).

cnf(c_15297,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X2_49,X3_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_7069,c_10379])).

cnf(c_35236,plain,
    ( ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X2_49,X3_49),X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X3_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15297,c_11671])).

cnf(c_35237,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X2_49,X3_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X2_49,X3_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_35236])).

cnf(c_35290,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X0_49,X2_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X2_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_35237,c_7051])).

cnf(c_35314,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X0_49,X2_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X2_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X2_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35290,c_7065,c_7064])).

cnf(c_17,plain,
    ( ~ sP2(X0,X1,X2,X3)
    | ~ r1_orders_2(X2,X3,X0)
    | ~ r1_orders_2(X2,X3,X1)
    | r1_orders_2(X2,sK7(X0,X1,X2,X3),X1)
    | r2_yellow_0(X2,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_831,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X3)
    | r1_orders_2(X0,sK7(X2,X3,X0,X1),X3)
    | r2_yellow_0(X0,k2_tarski(X3,X2))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ m1_subset_1(X5,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | X4 != X1
    | X5 != X3
    | X6 != X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_481])).

cnf(c_832,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X0,X2)
    | r1_orders_2(sK8,sK7(X2,X1,sK8,X0),X1)
    | r2_yellow_0(sK8,k2_tarski(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_7052,plain,
    ( ~ r1_orders_2(sK8,X0_49,X1_49)
    | ~ r1_orders_2(sK8,X0_49,X2_49)
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_35929,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X1_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X1_49),X0_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(sK6(sK8,X0_49,X1_49),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,sK6(sK8,X0_49,X1_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,sK6(sK8,X0_49,X1_49),X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_35314,c_7052])).

cnf(c_10093,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X1_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10054,c_7052])).

cnf(c_10766,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,X2_49,X1_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X2_49,X1_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10093,c_7065,c_7064])).

cnf(c_10792,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X0_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10766,c_7051])).

cnf(c_10803,plain,
    ( ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10792,c_7064,c_7063,c_7870])).

cnf(c_10804,plain,
    ( ~ r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_10803])).

cnf(c_15282,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_7069,c_7050])).

cnf(c_7576,plain,
    ( r1_orders_2(X0_48,X0_49,X1_49) != iProver_top
    | r1_orders_2(X0_48,X0_49,X2_49) != iProver_top
    | r1_orders_2(X0_48,X0_49,sK6(X0_48,X2_49,X1_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(X0_48)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(X0_48)) != iProver_top
    | sP0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7069])).

cnf(c_7595,plain,
    ( r1_orders_2(sK8,X0_49,X1_49) != iProver_top
    | r1_orders_2(sK8,X0_49,X2_49) != iProver_top
    | r1_orders_2(sK8,sK7(X2_49,X1_49,sK8,X0_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X2_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7050])).

cnf(c_10225,plain,
    ( r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) != iProver_top
    | r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49) != iProver_top
    | r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49) != iProver_top
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) = iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X3_49,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) != iProver_top
    | sP0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7576,c_7595])).

cnf(c_10354,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10225])).

cnf(c_15660,plain,
    ( ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15282,c_10354,c_11671])).

cnf(c_15661,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_15660])).

cnf(c_15677,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X3_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X2_49,X3_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X2_49,X3_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15661,c_7053])).

cnf(c_15718,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,sK6(sK8,X1_49,X2_49)),X2_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X1_49,X2_49),X1_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X1_49,X2_49),X0_49)
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X2_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_15677,c_7052])).

cnf(c_16589,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49)
    | ~ r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_15718,c_7051])).

cnf(c_11,plain,
    ( r1_orders_2(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7067,plain,
    ( r1_orders_2(X0_48,sK6(X0_48,X0_49,X1_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_8321,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(instantiation,[status(thm)],[c_7067])).

cnf(c_16602,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0_49,X1_49),X1_49)
    | r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16589,c_8321,c_11671])).

cnf(c_10,plain,
    ( r1_orders_2(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7068,plain,
    ( r1_orders_2(X0_48,sK6(X0_48,X0_49,X1_49),X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_16635,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_16602,c_7068])).

cnf(c_38580,plain,
    ( r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0_49,X1_49),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35929,c_10804,c_11671,c_16635])).

cnf(c_38581,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X1_49,X0_49),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_38580])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7066,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(X0_48))
    | ~ m1_subset_1(X1_49,u1_struct_0(X0_48))
    | m1_subset_1(sK6(X0_48,X1_49,X0_49),u1_struct_0(X0_48))
    | ~ sP0(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_38604,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_38581,c_7066])).

cnf(c_41526,plain,
    ( ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ r1_orders_2(X0_48,k11_lattice3(sK8,X0_49,X1_49),X2_49)
    | r1_orders_2(X0_48,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39795,c_7064,c_7063,c_7870,c_11671,c_38604])).

cnf(c_41527,plain,
    ( ~ r1_orders_2(X0_48,k11_lattice3(sK8,X0_49,X1_49),X2_49)
    | r1_orders_2(X0_48,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X1_49),X3_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_41526])).

cnf(c_10411,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X2_49,X3_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X2_49,X3_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_10379,c_7062])).

cnf(c_14307,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),X3_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X3_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X2_49,X3_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X3_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X3_49),X0_49)),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10411,c_7065])).

cnf(c_14345,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X2_49,X0_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49)),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14307,c_7051])).

cnf(c_14367,plain,
    ( ~ r1_orders_2(sK8,sK7(X0_49,X1_49,sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49)),X2_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X2_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X2_49,X0_49),X0_49))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,k11_lattice3(sK8,X2_49,X0_49),X0_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14345,c_7053])).

cnf(c_14956,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X0_49,X0_49),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14367,c_7051])).

cnf(c_14986,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X0_49,X0_49),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X0_49),u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_14956,c_7064])).

cnf(c_15500,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49),X1_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X0_49,X0_49),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X0_49),u1_struct_0(sK8)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14986,c_7065])).

cnf(c_42088,plain,
    ( ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X0_49),X1_49)
    | ~ r1_orders_2(sK8,k11_lattice3(sK8,X0_49,X0_49),X0_49)
    | ~ r2_yellow_0(sK8,k2_tarski(X0_49,X0_49))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49))
    | ~ r2_yellow_0(sK8,k2_tarski(k11_lattice3(sK8,X0_49,X0_49),X0_49))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(k11_lattice3(sK8,X0_49,X0_49),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_41527,c_15500])).

cnf(c_42111,plain,
    ( ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8))
    | r2_yellow_0(sK8,k2_tarski(X1_49,X0_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42088,c_10804,c_11671,c_38604])).

cnf(c_42112,plain,
    ( r2_yellow_0(sK8,k2_tarski(X0_49,X1_49))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_42111])).

cnf(c_43095,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_12221,c_42112])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_590,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_526,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_581,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ sP0(sK8) ),
    inference(resolution,[status(thm)],[c_526,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43095,c_11671,c_590,c_581])).


%------------------------------------------------------------------------------
