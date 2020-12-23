%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1529+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:47 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  179 (5312 expanded)
%              Number of clauses        :  128 (1406 expanded)
%              Number of leaves         :   11 (1584 expanded)
%              Depth                    :   30
%              Number of atoms          :  763 (40899 expanded)
%              Number of equality atoms :  264 (3551 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                   => r2_lattice3(X0,k1_tarski(X2),X1) )
                  & ( r2_lattice3(X0,k1_tarski(X2),X1)
                   => r1_orders_2(X0,X2,X1) )
                  & ( r1_orders_2(X0,X1,X2)
                   => r1_lattice3(X0,k1_tarski(X2),X1) )
                  & ( r1_lattice3(X0,k1_tarski(X2),X1)
                   => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | ( ~ r1_orders_2(X0,X1,X2)
                  & r1_lattice3(X0,k1_tarski(X2),X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ( ~ r1_orders_2(X0,X1,X2)
        & r1_lattice3(X0,k1_tarski(X2),X1) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | sP0(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
              & r1_orders_2(X0,X2,X1) )
            | ( ~ r1_orders_2(X0,X2,X1)
              & r2_lattice3(X0,k1_tarski(X2),X1) )
            | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
              & r1_orders_2(X0,X1,X2) )
            | sP0(X2,X1,X0) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,k1_tarski(sK6),X1)
            & r1_orders_2(X0,sK6,X1) )
          | ( ~ r1_orders_2(X0,sK6,X1)
            & r2_lattice3(X0,k1_tarski(sK6),X1) )
          | ( ~ r1_lattice3(X0,k1_tarski(sK6),X1)
            & r1_orders_2(X0,X1,sK6) )
          | sP0(sK6,X1,X0) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | sP0(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),sK5)
                & r1_orders_2(X0,X2,sK5) )
              | ( ~ r1_orders_2(X0,X2,sK5)
                & r2_lattice3(X0,k1_tarski(X2),sK5) )
              | ( ~ r1_lattice3(X0,k1_tarski(X2),sK5)
                & r1_orders_2(X0,sK5,X2) )
              | sP0(X2,sK5,X0) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X2,X1) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & r2_lattice3(X0,k1_tarski(X2),X1) )
                  | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X1,X2) )
                  | sP0(X2,X1,X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(sK4,k1_tarski(X2),X1)
                  & r1_orders_2(sK4,X2,X1) )
                | ( ~ r1_orders_2(sK4,X2,X1)
                  & r2_lattice3(sK4,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(sK4,k1_tarski(X2),X1)
                  & r1_orders_2(sK4,X1,X2) )
                | sP0(X2,X1,sK4) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
        & r1_orders_2(sK4,sK6,sK5) )
      | ( ~ r1_orders_2(sK4,sK6,sK5)
        & r2_lattice3(sK4,k1_tarski(sK6),sK5) )
      | ( ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
        & r1_orders_2(sK4,sK5,sK6) )
      | sP0(sK6,sK5,sK4) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f29,f28,f27])).

fof(f46,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(flattening,[],[f6])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(flattening,[],[f8])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( ~ r1_orders_2(X0,X1,X2)
        & r1_lattice3(X0,k1_tarski(X2),X1) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X2,X1,X0)
        & r1_lattice3(X2,k1_tarski(X0),X1) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X2,k1_tarski(X0),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | sP0(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X2,X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
    | sP0(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( r1_orders_2(sK4,sK6,sK5)
    | r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
    | sP0(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( r1_orders_2(sK4,sK6,sK5)
    | r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | sP0(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2819,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_335,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_336,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_2813,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2822,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_284,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_285,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_2816,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2821,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3746,plain,
    ( sK3(sK4,k1_tarski(X0),X1) = X0
    | r2_lattice3(sK4,k1_tarski(X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_2821])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_248,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_249,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_2818,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_4174,plain,
    ( sK3(sK4,k1_tarski(X0),X1) = X0
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3746,c_2818])).

cnf(c_5308,plain,
    ( sK3(sK4,k1_tarski(X0),X1) = X0
    | r1_orders_2(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2822,c_4174])).

cnf(c_5919,plain,
    ( sK3(sK4,k1_tarski(X0),sK2(sK4,X1,X2)) = X0
    | r1_orders_2(sK4,X0,sK2(sK4,X1,X2)) = iProver_top
    | r1_lattice3(sK4,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2813,c_5308])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_365,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_366,plain,
    ( ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
    | r1_lattice3(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_2811,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1,X0)) != iProver_top
    | r1_lattice3(sK4,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_7291,plain,
    ( sK3(sK4,k1_tarski(X0),sK2(sK4,X1,X0)) = X0
    | r1_lattice3(sK4,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5919,c_2811])).

cnf(c_7424,plain,
    ( sK3(sK4,k1_tarski(sK5),sK2(sK4,X0,sK5)) = sK5
    | r1_lattice3(sK4,X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_7291])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_lattice3(X2,k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( sP0(sK6,sK5,sK4)
    | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_434,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | r1_lattice3(X0,k1_tarski(X1),X2)
    | sK5 != X2
    | sK6 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_435,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_2809,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_26,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_436,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_3259,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3264,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3259])).

cnf(c_3045,plain,
    ( ~ r2_lattice3(sK4,X0,sK5)
    | r1_orders_2(sK4,X1,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_3248,plain,
    ( ~ r2_lattice3(sK4,X0,sK5)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_3480,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_3484,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3480])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_314,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_315,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ r1_lattice3(sK4,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_3050,plain,
    ( r1_orders_2(sK4,X0,sK6)
    | ~ r1_lattice3(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,X1) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_3258,plain,
    ( r1_orders_2(sK4,X0,sK6)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_3495,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_3496,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3495])).

cnf(c_3871,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2809,c_26,c_27,c_436,c_3264,c_3484,c_3496])).

cnf(c_4172,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3746,c_3871])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_orders_2(X2,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( sP0(sK6,sK5,sK4)
    | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_472,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
    | sK5 != X1
    | sK6 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_473,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_2807,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_4173,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3746,c_2807])).

cnf(c_4200,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4172,c_4173])).

cnf(c_2820,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5917,plain,
    ( sK3(sK4,k1_tarski(X0),sK5) = X0
    | r1_orders_2(sK4,X0,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_5308])).

cnf(c_6261,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_5917])).

cnf(c_7772,plain,
    ( r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4200,c_26,c_6261])).

cnf(c_7773,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7772])).

cnf(c_7779,plain,
    ( sK3(sK4,k1_tarski(sK5),sK2(sK4,k1_tarski(sK6),sK5)) = sK5
    | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(superposition,[status(thm)],[c_7424,c_7773])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_299,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_300,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_2815,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_7883,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r2_lattice3(sK4,k1_tarski(sK5),sK2(sK4,k1_tarski(sK6),sK5)) = iProver_top
    | r1_orders_2(sK4,sK5,sK2(sK4,k1_tarski(sK6),sK5)) != iProver_top
    | m1_subset_1(sK2(sK4,k1_tarski(sK6),sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7779,c_2815])).

cnf(c_474,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_3001,plain,
    ( r2_lattice3(sK4,X0,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_3698,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3001])).

cnf(c_3705,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3698])).

cnf(c_3192,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK6))
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4570,plain,
    ( ~ r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6))
    | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(instantiation,[status(thm)],[c_3192])).

cnf(c_4571,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4570])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_350,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_351,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_2812,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_3738,plain,
    ( sK2(sK4,k1_tarski(X0),X1) = X0
    | r1_lattice3(sK4,k1_tarski(X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_2821])).

cnf(c_7778,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3738,c_7773])).

cnf(c_7997,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7778,c_26])).

cnf(c_7998,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
    | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(renaming,[status(thm)],[c_7997])).

cnf(c_8011,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7998,c_2815])).

cnf(c_923,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X1,X0),X1)
    | k1_tarski(sK6) != X1
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_473,c_351])).

cnf(c_924,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_926,plain,
    ( ~ r1_orders_2(sK4,sK6,sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_23])).

cnf(c_927,plain,
    ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | ~ r1_orders_2(sK4,sK6,sK5)
    | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
    inference(renaming,[status(thm)],[c_926])).

cnf(c_928,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_2814,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_3099,plain,
    ( r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_2814])).

cnf(c_3155,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,X0,sK5) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_3099])).

cnf(c_4026,plain,
    ( sK2(sK4,k1_tarski(X0),sK5) = X0
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3738,c_3155])).

cnf(c_4722,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | sK2(sK4,k1_tarski(X0),sK5) = X0
    | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4026,c_26])).

cnf(c_4723,plain,
    ( sK2(sK4,k1_tarski(X0),sK5) = X0
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4722])).

cnf(c_4731,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2822,c_4723])).

cnf(c_4794,plain,
    ( ~ r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6))
    | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(instantiation,[status(thm)],[c_3192])).

cnf(c_4795,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4794])).

cnf(c_20,negated_conjecture,
    ( sP0(sK6,sK5,sK4)
    | r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_454,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
    | sK5 != X1
    | sK6 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_455,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | ~ r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_2808,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_4022,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3738,c_2808])).

cnf(c_21,negated_conjecture,
    ( sP0(sK6,sK5,sK4)
    | r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_416,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r1_lattice3(X0,k1_tarski(X1),X2)
    | sK5 != X2
    | sK6 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_417,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
    | r1_orders_2(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK6,sK5)
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_2810,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_418,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_4478,plain,
    ( r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2810,c_26,c_27,c_418,c_3264,c_3484,c_3496])).

cnf(c_4479,plain,
    ( r1_orders_2(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4478])).

cnf(c_4861,plain,
    ( r1_orders_2(sK4,sK6,sK5) = iProver_top
    | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4022,c_26,c_27,c_418,c_3264,c_3484,c_3496])).

cnf(c_4862,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_4861])).

cnf(c_8394,plain,
    ( sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8011,c_26,c_928,c_4731,c_4795,c_4862])).

cnf(c_8408,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8394,c_2811])).

cnf(c_8618,plain,
    ( r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8408,c_26])).

cnf(c_8619,plain,
    ( r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_8618])).

cnf(c_3100,plain,
    ( r1_orders_2(sK4,X0,sK5) = iProver_top
    | r1_lattice3(sK4,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_2814])).

cnf(c_3539,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | r1_lattice3(sK4,X0,sK5) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_3100])).

cnf(c_8626,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r2_hidden(sK5,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8619,c_3539])).

cnf(c_8654,plain,
    ( r1_orders_2(sK4,sK5,sK5) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK5,k1_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_8626])).

cnf(c_8625,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8619,c_2808])).

cnf(c_8838,plain,
    ( r1_orders_2(sK4,sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8654,c_26,c_27,c_3264,c_3484,c_4479,c_8625])).

cnf(c_9335,plain,
    ( sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7883,c_26,c_27,c_474,c_3264,c_3484,c_3705,c_3871,c_4479,c_4571,c_8408,c_8625])).

cnf(c_9349,plain,
    ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
    | r1_orders_2(sK4,sK6,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9335,c_2815])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9349,c_8838,c_8408,c_3871,c_474,c_26])).


%------------------------------------------------------------------------------
