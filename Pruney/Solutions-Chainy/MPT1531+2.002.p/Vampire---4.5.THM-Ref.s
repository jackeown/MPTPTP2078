%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 768 expanded)
%              Number of leaves         :   10 ( 294 expanded)
%              Depth                    :   23
%              Number of atoms          :  389 (5555 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(subsumption_resolution,[],[f379,f336])).

fof(f336,plain,(
    r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f331,f68])).

fof(f68,plain,(
    ! [X5] :
      ( r1_lattice3(sK0,X5,sK3)
      | r2_hidden(sK4(sK0,X5,sK3),X5) ) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
        & r2_lattice3(sK0,sK2,sK3) )
      | ( ~ r1_lattice3(sK0,sK1,sK3)
        & r1_lattice3(sK0,sK2,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f14,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
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

fof(f14,plain,
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f58,plain,(
    ! [X5] :
      ( r1_lattice3(sK0,X5,sK3)
      | r2_hidden(sK4(sK0,X5,sK3),X5)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f30,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f331,plain,(
    ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f330,f100])).

fof(f100,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f99,f28])).

fof(f99,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f34,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f330,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f329,f32])).

fof(f32,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f329,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f179,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ r1_lattice3(sK0,sK1,sK3)
      | ~ r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f98,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f28])).

fof(f97,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f94,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f177,f28])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f30])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f102,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f101,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f96,f30])).

fof(f96,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f379,plain,(
    ~ r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f368,f54])).

fof(f368,plain,(
    ~ r2_hidden(sK4(sK0,sK1,sK3),sK2) ),
    inference(global_subsumption,[],[f345,f356])).

fof(f356,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3)) ),
    inference(resolution,[],[f335,f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r1_orders_2(sK0,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f271,f28])).

fof(f271,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3,X0)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f30])).

fof(f270,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3,X0)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f269,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f269,plain,(
    r1_lattice3(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f268,f91])).

fof(f91,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f90,f28])).

fof(f90,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f86,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f33,f41])).

fof(f33,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f268,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f267,f31])).

fof(f31,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f267,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f160,f54])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | r1_lattice3(sK0,sK2,sK3)
      | ~ r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f159,f89])).

fof(f89,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f88,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f85,f30])).

fof(f85,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f33,f40])).

fof(f159,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f158,f28])).

fof(f158,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f30])).

fof(f156,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,sK3)
      | ~ r2_hidden(sK5(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f93,f39])).

fof(f93,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f92,f28])).

fof(f92,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f335,plain,(
    m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f331,f67])).

fof(f67,plain,(
    ! [X4] :
      ( r1_lattice3(sK0,X4,sK3)
      | m1_subset_1(sK4(sK0,X4,sK3),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,(
    ! [X4] :
      ( r1_lattice3(sK0,X4,sK3)
      | m1_subset_1(sK4(sK0,X4,sK3),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f345,plain,(
    ~ r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f344,f28])).

fof(f344,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f339,f30])).

fof(f339,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f331,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:56 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.43  % (6848)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.44  % (6848)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f381,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f379,f336])).
% 0.21/0.44  fof(f336,plain,(
% 0.21/0.44    r2_hidden(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(resolution,[],[f331,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X5] : (r1_lattice3(sK0,X5,sK3) | r2_hidden(sK4(sK0,X5,sK3),X5)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f58,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    l1_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ((((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f14,f13,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0)) => (? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) & l1_orders_2(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X2,X1] : (? [X3] : (((~r2_lattice3(sK0,X1,X3) & r2_lattice3(sK0,X2,X3)) | (~r1_lattice3(sK0,X1,X3) & r1_lattice3(sK0,X2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(X1,X2)) => (? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & r1_tarski(sK1,sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X3] : (((~r2_lattice3(sK0,sK1,X3) & r2_lattice3(sK0,sK2,X3)) | (~r1_lattice3(sK0,sK1,X3) & r1_lattice3(sK0,sK2,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,sK1,sK3) & r2_lattice3(sK0,sK2,sK3)) | (~r1_lattice3(sK0,sK1,sK3) & r1_lattice3(sK0,sK2,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0] : (? [X1,X2] : (? [X3] : (((~r2_lattice3(X0,X1,X3) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X0,X1,X3) & r1_lattice3(X0,X2,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_tarski(X1,X2)) & l1_orders_2(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X5] : (r1_lattice3(sK0,X5,sK3) | r2_hidden(sK4(sK0,X5,sK3),X5) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f30,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(rectify,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f331,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f330,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f99,f28])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f95,f30])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f34,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(rectify,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~r2_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f330,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f329,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f329,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(resolution,[],[f179,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.44    inference(resolution,[],[f29,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    r1_tarski(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~r1_lattice3(sK0,sK1,sK3) | ~r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f178,f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f97,f28])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f94,f30])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f34,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f177,f28])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f175,f30])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f102,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f101,f28])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f96,f30])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ~r1_lattice3(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f34,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f379,plain,(
% 0.21/0.44    ~r2_hidden(sK4(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(resolution,[],[f368,f54])).
% 0.21/0.44  fof(f368,plain,(
% 0.21/0.44    ~r2_hidden(sK4(sK0,sK1,sK3),sK2)),
% 0.21/0.44    inference(global_subsumption,[],[f345,f356])).
% 0.21/0.44  fof(f356,plain,(
% 0.21/0.44    ~r2_hidden(sK4(sK0,sK1,sK3),sK2) | r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))),
% 0.21/0.44    inference(resolution,[],[f335,f272])).
% 0.21/0.44  fof(f272,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,sK3,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f271,f28])).
% 0.21/0.44  fof(f271,plain,(
% 0.21/0.44    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f270,f30])).
% 0.21/0.44  fof(f270,plain,(
% 0.21/0.44    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f269,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f269,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f268,f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f90,f28])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f86,f30])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f33,f41])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ~r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f268,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(subsumption_resolution,[],[f267,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f267,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.21/0.44    inference(resolution,[],[f160,f54])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(sK5(sK0,sK1,sK3),X0) | r1_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f159,f89])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.44    inference(subsumption_resolution,[],[f88,f28])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f85,f30])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f33,f40])).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ( ! [X0] : (r1_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f158,f28])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ( ! [X0] : (r1_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f156,f30])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X0] : (r1_lattice3(sK0,sK2,sK3) | ~r2_hidden(sK5(sK0,sK1,sK3),X0) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f93,f39])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f92,f28])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f87,f30])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    r1_lattice3(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f33,f42])).
% 0.21/0.44  fof(f335,plain,(
% 0.21/0.44    m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.44    inference(resolution,[],[f331,f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | m1_subset_1(sK4(sK0,X4,sK3),u1_struct_0(sK0))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f57,f28])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | m1_subset_1(sK4(sK0,X4,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f30,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f345,plain,(
% 0.21/0.44    ~r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3))),
% 0.21/0.44    inference(subsumption_resolution,[],[f344,f28])).
% 0.21/0.44  fof(f344,plain,(
% 0.21/0.44    ~r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f339,f30])).
% 0.21/0.44  fof(f339,plain,(
% 0.21/0.44    ~r1_orders_2(sK0,sK3,sK4(sK0,sK1,sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.44    inference(resolution,[],[f331,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (6848)------------------------------
% 0.21/0.44  % (6848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (6848)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (6848)Memory used [KB]: 5628
% 0.21/0.44  % (6848)Time elapsed: 0.036 s
% 0.21/0.44  % (6848)------------------------------
% 0.21/0.44  % (6848)------------------------------
% 0.21/0.45  % (6836)Success in time 0.089 s
%------------------------------------------------------------------------------
