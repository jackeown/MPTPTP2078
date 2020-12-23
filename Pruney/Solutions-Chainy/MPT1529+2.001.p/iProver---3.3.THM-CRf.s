%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:26 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.88/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/0.98  
% 2.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.98  
% 2.88/0.98  ------  iProver source info
% 2.88/0.98  
% 2.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.98  git: non_committed_changes: false
% 2.88/0.98  git: last_make_outside_of_git: false
% 2.88/0.98  
% 2.88/0.98  ------ 
% 2.88/0.98  
% 2.88/0.98  ------ Input Options
% 2.88/0.98  
% 2.88/0.98  --out_options                           all
% 2.88/0.98  --tptp_safe_out                         true
% 2.88/0.98  --problem_path                          ""
% 2.88/0.98  --include_path                          ""
% 2.88/0.98  --clausifier                            res/vclausify_rel
% 2.88/0.98  --clausifier_options                    --mode clausify
% 2.88/0.98  --stdin                                 false
% 2.88/0.98  --stats_out                             all
% 2.88/0.98  
% 2.88/0.98  ------ General Options
% 2.88/0.98  
% 2.88/0.98  --fof                                   false
% 2.88/0.98  --time_out_real                         305.
% 2.88/0.98  --time_out_virtual                      -1.
% 2.88/0.98  --symbol_type_check                     false
% 2.88/0.98  --clausify_out                          false
% 2.88/0.98  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     num_symb
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       true
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  ------ Parsing...
% 2.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.99  ------ Proving...
% 2.88/0.99  ------ Problem Properties 
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  clauses                                 18
% 2.88/0.99  conjectures                             2
% 2.88/0.99  EPR                                     0
% 2.88/0.99  Horn                                    10
% 2.88/0.99  unary                                   3
% 2.88/0.99  binary                                  1
% 2.88/0.99  lits                                    55
% 2.88/0.99  lits eq                                 5
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 0
% 2.88/0.99  fd_pseudo_cond                          2
% 2.88/0.99  AC symbols                              0
% 2.88/0.99  
% 2.88/0.99  ------ Schedule dynamic 5 is on 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  Current options:
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     none
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       false
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ Proving...
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS status Theorem for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  fof(f4,conjecture,(
% 2.88/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f5,negated_conjecture,(
% 2.88/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.88/0.99    inference(negated_conjecture,[],[f4])).
% 2.88/0.99  
% 2.88/0.99  fof(f10,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | (~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 2.88/0.99    inference(ennf_transformation,[],[f5])).
% 2.88/0.99  
% 2.88/0.99  fof(f11,plain,(
% 2.88/0.99    ! [X2,X1,X0] : ((~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1)) | ~sP0(X2,X1,X0))),
% 2.88/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.88/0.99  
% 2.88/0.99  fof(f12,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | sP0(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 2.88/0.99    inference(definition_folding,[],[f10,f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f29,plain,(
% 2.88/0.99    ( ! [X0,X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | sP0(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (((~r2_lattice3(X0,k1_tarski(sK6),X1) & r1_orders_2(X0,sK6,X1)) | (~r1_orders_2(X0,sK6,X1) & r2_lattice3(X0,k1_tarski(sK6),X1)) | (~r1_lattice3(X0,k1_tarski(sK6),X1) & r1_orders_2(X0,X1,sK6)) | sP0(sK6,X1,X0)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f28,plain,(
% 2.88/0.99    ( ! [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | sP0(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),sK5) & r1_orders_2(X0,X2,sK5)) | (~r1_orders_2(X0,X2,sK5) & r2_lattice3(X0,k1_tarski(X2),sK5)) | (~r1_lattice3(X0,k1_tarski(X2),sK5) & r1_orders_2(X0,sK5,X2)) | sP0(X2,sK5,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f27,plain,(
% 2.88/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | sP0(X2,X1,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (((~r2_lattice3(sK4,k1_tarski(X2),X1) & r1_orders_2(sK4,X2,X1)) | (~r1_orders_2(sK4,X2,X1) & r2_lattice3(sK4,k1_tarski(X2),X1)) | (~r1_lattice3(sK4,k1_tarski(X2),X1) & r1_orders_2(sK4,X1,X2)) | sP0(X2,X1,sK4)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f30,plain,(
% 2.88/0.99    ((((~r2_lattice3(sK4,k1_tarski(sK6),sK5) & r1_orders_2(sK4,sK6,sK5)) | (~r1_orders_2(sK4,sK6,sK5) & r2_lattice3(sK4,k1_tarski(sK6),sK5)) | (~r1_lattice3(sK4,k1_tarski(sK6),sK5) & r1_orders_2(sK4,sK5,sK6)) | sP0(sK6,sK5,sK4)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f12,f29,f28,f27])).
% 2.88/0.99  
% 2.88/0.99  fof(f46,plain,(
% 2.88/0.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f2,axiom,(
% 2.88/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f6,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(ennf_transformation,[],[f2])).
% 2.88/0.99  
% 2.88/0.99  fof(f7,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(flattening,[],[f6])).
% 2.88/0.99  
% 2.88/0.99  fof(f17,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f7])).
% 2.88/0.99  
% 2.88/0.99  fof(f18,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(rectify,[],[f17])).
% 2.88/0.99  
% 2.88/0.99  fof(f19,plain,(
% 2.88/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f20,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 2.88/0.99  
% 2.88/0.99  fof(f36,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f45,plain,(
% 2.88/0.99    l1_orders_2(sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f1,axiom,(
% 2.88/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f13,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(nnf_transformation,[],[f1])).
% 2.88/0.99  
% 2.88/0.99  fof(f14,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(rectify,[],[f13])).
% 2.88/0.99  
% 2.88/0.99  fof(f15,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f16,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 2.88/0.99  
% 2.88/0.99  fof(f32,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f56,plain,(
% 2.88/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.88/0.99    inference(equality_resolution,[],[f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f57,plain,(
% 2.88/0.99    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.88/0.99    inference(equality_resolution,[],[f56])).
% 2.88/0.99  
% 2.88/0.99  fof(f3,axiom,(
% 2.88/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f8,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(ennf_transformation,[],[f3])).
% 2.88/0.99  
% 2.88/0.99  fof(f9,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(flattening,[],[f8])).
% 2.88/0.99  
% 2.88/0.99  fof(f21,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f9])).
% 2.88/0.99  
% 2.88/0.99  fof(f22,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(rectify,[],[f21])).
% 2.88/0.99  
% 2.88/0.99  fof(f23,plain,(
% 2.88/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f24,plain,(
% 2.88/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f41,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f24])).
% 2.88/0.99  
% 2.88/0.99  fof(f31,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.88/0.99    inference(cnf_transformation,[],[f16])).
% 2.88/0.99  
% 2.88/0.99  fof(f58,plain,(
% 2.88/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.88/0.99    inference(equality_resolution,[],[f31])).
% 2.88/0.99  
% 2.88/0.99  fof(f39,plain,(
% 2.88/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f24])).
% 2.88/0.99  
% 2.88/0.99  fof(f38,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f25,plain,(
% 2.88/0.99    ! [X2,X1,X0] : ((~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1)) | ~sP0(X2,X1,X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f26,plain,(
% 2.88/0.99    ! [X0,X1,X2] : ((~r1_orders_2(X2,X1,X0) & r1_lattice3(X2,k1_tarski(X0),X1)) | ~sP0(X0,X1,X2))),
% 2.88/0.99    inference(rectify,[],[f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f43,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X2,k1_tarski(X0),X1) | ~sP0(X0,X1,X2)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f26])).
% 2.88/0.99  
% 2.88/0.99  fof(f54,plain,(
% 2.88/0.99    ~r2_lattice3(sK4,k1_tarski(sK6),sK5) | ~r1_orders_2(sK4,sK6,sK5) | r1_orders_2(sK4,sK5,sK6) | sP0(sK6,sK5,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f47,plain,(
% 2.88/0.99    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f35,plain,(
% 2.88/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f44,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (~r1_orders_2(X2,X1,X0) | ~sP0(X0,X1,X2)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f26])).
% 2.88/0.99  
% 2.88/0.99  fof(f55,plain,(
% 2.88/0.99    ~r2_lattice3(sK4,k1_tarski(sK6),sK5) | ~r1_orders_2(sK4,sK6,sK5) | ~r1_lattice3(sK4,k1_tarski(sK6),sK5) | sP0(sK6,sK5,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f42,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f24])).
% 2.88/0.99  
% 2.88/0.99  fof(f37,plain,(
% 2.88/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f49,plain,(
% 2.88/0.99    r1_orders_2(sK4,sK6,sK5) | r2_lattice3(sK4,k1_tarski(sK6),sK5) | ~r1_lattice3(sK4,k1_tarski(sK6),sK5) | sP0(sK6,sK5,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f48,plain,(
% 2.88/0.99    r1_orders_2(sK4,sK6,sK5) | r2_lattice3(sK4,k1_tarski(sK6),sK5) | r1_orders_2(sK4,sK5,sK6) | sP0(sK6,sK5,sK4)),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  cnf(c_23,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2819,plain,
% 2.88/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_6,plain,
% 2.88/0.99      ( r1_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_24,negated_conjecture,
% 2.88/0.99      ( l1_orders_2(sK4) ),
% 2.88/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_335,plain,
% 2.88/0.99      ( r1_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_336,plain,
% 2.88/0.99      ( r1_lattice3(sK4,X0,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_335]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2813,plain,
% 2.88/0.99      ( r1_lattice3(sK4,X0,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2,plain,
% 2.88/0.99      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2822,plain,
% 2.88/0.99      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9,plain,
% 2.88/0.99      ( r2_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_284,plain,
% 2.88/0.99      ( r2_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | r2_hidden(sK3(X0,X1,X2),X1)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_285,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK3(sK4,X0,X1),X0) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2816,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.88/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2821,plain,
% 2.88/0.99      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3746,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),X1) = X0
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(X0),X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2816,c_2821]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_11,plain,
% 2.88/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.88/0.99      | r1_orders_2(X0,X3,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ r2_hidden(X3,X1)
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_248,plain,
% 2.88/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 2.88/0.99      | r1_orders_2(X0,X3,X2)
% 2.88/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ r2_hidden(X3,X1)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_249,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,X0,X1)
% 2.88/0.99      | r1_orders_2(sK4,X2,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(X2,X0) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_248]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2818,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,X2,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4174,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),X1) = X0
% 2.88/0.99      | r1_orders_2(sK4,X2,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(X2,k1_tarski(X0)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3746,c_2818]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5308,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),X1) = X0
% 2.88/0.99      | r1_orders_2(sK4,X0,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2822,c_4174]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5919,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),sK2(sK4,X1,X2)) = X0
% 2.88/0.99      | r1_orders_2(sK4,X0,sK2(sK4,X1,X2)) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X1,X2) = iProver_top
% 2.88/0.99      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2813,c_5308]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4,plain,
% 2.88/0.99      ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
% 2.88/0.99      | r1_lattice3(X0,X2,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_365,plain,
% 2.88/0.99      ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
% 2.88/0.99      | r1_lattice3(X0,X2,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_366,plain,
% 2.88/0.99      ( ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
% 2.88/0.99      | r1_lattice3(sK4,X1,X0)
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_365]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2811,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,sK2(sK4,X1,X0)) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X1,X0) = iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7291,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),sK2(sK4,X1,X0)) = X0
% 2.88/0.99      | r1_lattice3(sK4,X1,X0) = iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_5919,c_2811]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7424,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK5),sK2(sK4,X0,sK5)) = sK5
% 2.88/0.99      | r1_lattice3(sK4,X0,sK5) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2819,c_7291]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_13,plain,
% 2.88/0.99      ( ~ sP0(X0,X1,X2) | r1_lattice3(X2,k1_tarski(X0),X1) ),
% 2.88/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_15,negated_conjecture,
% 2.88/0.99      ( sP0(sK6,sK5,sK4)
% 2.88/0.99      | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_434,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | r1_lattice3(X0,k1_tarski(X1),X2)
% 2.88/0.99      | sK5 != X2
% 2.88/0.99      | sK6 != X1
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_435,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2809,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_26,plain,
% 2.88/0.99      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_22,negated_conjecture,
% 2.88/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_27,plain,
% 2.88/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_436,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3259,plain,
% 2.88/0.99      ( r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3264,plain,
% 2.88/0.99      ( r2_hidden(sK6,k1_tarski(sK6)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3259]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3045,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,X0,sK5)
% 2.88/0.99      | r1_orders_2(sK4,X1,sK5)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(X1,X0) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_249]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3248,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,X0,sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(sK6,X0) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3045]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3480,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3248]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3484,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3480]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7,plain,
% 2.88/0.99      ( r1_orders_2(X0,X1,X2)
% 2.88/0.99      | ~ r1_lattice3(X0,X3,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ r2_hidden(X2,X3)
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_314,plain,
% 2.88/0.99      ( r1_orders_2(X0,X1,X2)
% 2.88/0.99      | ~ r1_lattice3(X0,X3,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ r2_hidden(X2,X3)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_315,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,X1)
% 2.88/0.99      | ~ r1_lattice3(sK4,X2,X0)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(X1,X2) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_314]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3050,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,sK6)
% 2.88/0.99      | ~ r1_lattice3(sK4,X1,X0)
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(sK6,X1) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_315]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3258,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,sK6)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),X0)
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3050]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3495,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.88/0.99      | ~ r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3258]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3496,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK6,k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3495]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3871,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2809,c_26,c_27,c_436,c_3264,c_3484,c_3496]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4172,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3746,c_3871]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_12,plain,
% 2.88/0.99      ( ~ sP0(X0,X1,X2) | ~ r1_orders_2(X2,X1,X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_14,negated_conjecture,
% 2.88/0.99      ( sP0(sK6,sK5,sK4)
% 2.88/0.99      | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_472,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(X0,X1,X2)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | sK5 != X1
% 2.88/0.99      | sK6 != X2
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_473,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_472]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2807,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4173,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3746,c_2807]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4200,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(backward_subsumption_resolution,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4172,c_4173]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2820,plain,
% 2.88/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5917,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(X0),sK5) = X0
% 2.88/0.99      | r1_orders_2(sK4,X0,sK5) = iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2819,c_5308]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_6261,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2820,c_5917]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7772,plain,
% 2.88/0.99      ( r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4200,c_26,c_6261]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7773,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_7772]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7779,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK5),sK2(sK4,k1_tarski(sK6),sK5)) = sK5
% 2.88/0.99      | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_7424,c_7773]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8,plain,
% 2.88/0.99      ( r2_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_299,plain,
% 2.88/0.99      ( r2_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_300,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,X1)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_299]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2815,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7883,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(sK5),sK2(sK4,k1_tarski(sK6),sK5)) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK2(sK4,k1_tarski(sK6),sK5)) != iProver_top
% 2.88/0.99      | m1_subset_1(sK2(sK4,k1_tarski(sK6),sK5),u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_7779,c_2815]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_474,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3001,plain,
% 2.88/0.99      ( r2_lattice3(sK4,X0,sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK3(sK4,X0,sK5),X0) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_285]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3698,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3001]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3705,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3698]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3192,plain,
% 2.88/0.99      ( ~ r2_hidden(X0,k1_tarski(sK6)) | X0 = sK6 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4570,plain,
% 2.88/0.99      ( ~ r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6))
% 2.88/0.99      | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3192]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4571,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r2_hidden(sK3(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_4570]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_5,plain,
% 2.88/0.99      ( r1_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 2.88/0.99      | ~ l1_orders_2(X0) ),
% 2.88/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_350,plain,
% 2.88/0.99      ( r1_lattice3(X0,X1,X2)
% 2.88/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.88/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_351,plain,
% 2.88/0.99      ( r1_lattice3(sK4,X0,X1)
% 2.88/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK2(sK4,X0,X1),X0) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_350]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2812,plain,
% 2.88/0.99      ( r1_lattice3(sK4,X0,X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3738,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(X0),X1) = X0
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(X0),X1) = iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2812,c_2821]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7778,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3738,c_7773]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7997,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_7778,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_7998,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_7997]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8011,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_7998,c_2815]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_923,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK2(sK4,X1,X0),X1)
% 2.88/0.99      | k1_tarski(sK6) != X1
% 2.88/0.99      | sK5 != X0
% 2.88/0.99      | sK4 != sK4 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_473,c_351]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_924,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.88/0.99      | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_923]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_926,plain,
% 2.88/0.99      ( ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_924,c_23]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_927,plain,
% 2.88/0.99      ( ~ r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_926]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_928,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2814,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X2,X0) != iProver_top
% 2.88/0.99      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(X1,X2) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3099,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,sK6) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X1,X0) != iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK6,X1) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2820,c_2814]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3155,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X0,sK5) != iProver_top
% 2.88/0.99      | r2_hidden(sK6,X0) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2819,c_3099]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4026,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(X0),sK5) = X0
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3738,c_3155]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4722,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | sK2(sK4,k1_tarski(X0),sK5) = X0
% 2.88/0.99      | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4026,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4723,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(X0),sK5) = X0
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r2_hidden(sK6,k1_tarski(X0)) != iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_4722]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4731,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2822,c_4723]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4794,plain,
% 2.88/0.99      ( ~ r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6))
% 2.88/0.99      | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(instantiation,[status(thm)],[c_3192]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4795,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r2_hidden(sK2(sK4,k1_tarski(sK6),sK5),k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_4794]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_20,negated_conjecture,
% 2.88/0.99      ( sP0(sK6,sK5,sK4)
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_454,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(X0,X1,X2)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | sK5 != X1
% 2.88/0.99      | sK6 != X2
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_455,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | ~ r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | ~ r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_454]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2808,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) != iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4022,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_3738,c_2808]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_21,negated_conjecture,
% 2.88/0.99      ( sP0(sK6,sK5,sK4)
% 2.88/0.99      | r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) ),
% 2.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_416,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | r1_lattice3(X0,k1_tarski(X1),X2)
% 2.88/0.99      | sK5 != X2
% 2.88/0.99      | sK6 != X1
% 2.88/0.99      | sK4 != X0 ),
% 2.88/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_417,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5)
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6)
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5)
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) ),
% 2.88/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_2810,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_418,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
% 2.88/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4478,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_2810,c_26,c_27,c_418,c_3264,c_3484,c_3496]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4479,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_4478]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4861,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_4022,c_26,c_27,c_418,c_3264,c_3484,c_3496]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4862,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_4861]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8394,plain,
% 2.88/0.99      ( sK2(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_8011,c_26,c_928,c_4731,c_4795,c_4862]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8408,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8394,c_2811]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8618,plain,
% 2.88/0.99      ( r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_8408,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8619,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top ),
% 2.88/0.99      inference(renaming,[status(thm)],[c_8618]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3100,plain,
% 2.88/0.99      ( r1_orders_2(sK4,X0,sK5) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X1,X0) != iProver_top
% 2.88/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 2.88/0.99      | r2_hidden(sK5,X1) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2819,c_2814]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_3539,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK5) = iProver_top
% 2.88/0.99      | r1_lattice3(sK4,X0,sK5) != iProver_top
% 2.88/0.99      | r2_hidden(sK5,X0) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_2819,c_3100]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8626,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r2_hidden(sK5,k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8619,c_3539]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8654,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK5,sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top
% 2.88/0.99      | r2_hidden(sK5,k1_tarski(sK6)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_4479,c_8626]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8625,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK5,sK6) != iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_8619,c_2808]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_8838,plain,
% 2.88/0.99      ( r1_orders_2(sK4,sK6,sK5) = iProver_top ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_8654,c_26,c_27,c_3264,c_3484,c_4479,c_8625]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9335,plain,
% 2.88/0.99      ( sK3(sK4,k1_tarski(sK6),sK5) = sK6 ),
% 2.88/0.99      inference(global_propositional_subsumption,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_7883,c_26,c_27,c_474,c_3264,c_3484,c_3705,c_3871,
% 2.88/0.99                 c_4479,c_4571,c_8408,c_8625]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_9349,plain,
% 2.88/0.99      ( r2_lattice3(sK4,k1_tarski(sK6),sK5) = iProver_top
% 2.88/0.99      | r1_orders_2(sK4,sK6,sK5) != iProver_top
% 2.88/0.99      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.88/0.99      inference(superposition,[status(thm)],[c_9335,c_2815]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(contradiction,plain,
% 2.88/0.99      ( $false ),
% 2.88/0.99      inference(minisat,
% 2.88/0.99                [status(thm)],
% 2.88/0.99                [c_9349,c_8838,c_8408,c_3871,c_474,c_26]) ).
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  ------                               Statistics
% 2.88/0.99  
% 2.88/0.99  ------ General
% 2.88/0.99  
% 2.88/0.99  abstr_ref_over_cycles:                  0
% 2.88/0.99  abstr_ref_under_cycles:                 0
% 2.88/0.99  gc_basic_clause_elim:                   0
% 2.88/0.99  forced_gc_time:                         0
% 2.88/0.99  parsing_time:                           0.01
% 2.88/0.99  unif_index_cands_time:                  0.
% 2.88/0.99  unif_index_add_time:                    0.
% 2.88/0.99  orderings_time:                         0.
% 2.88/0.99  out_proof_time:                         0.013
% 2.88/0.99  total_time:                             0.26
% 2.88/0.99  num_of_symbols:                         46
% 2.88/0.99  num_of_terms:                           5967
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing
% 2.88/0.99  
% 2.88/0.99  num_of_splits:                          0
% 2.88/0.99  num_of_split_atoms:                     0
% 2.88/0.99  num_of_reused_defs:                     0
% 2.88/0.99  num_eq_ax_congr_red:                    20
% 2.88/0.99  num_of_sem_filtered_clauses:            1
% 2.88/0.99  num_of_subtypes:                        0
% 2.88/0.99  monotx_restored_types:                  0
% 2.88/0.99  sat_num_of_epr_types:                   0
% 2.88/0.99  sat_num_of_non_cyclic_types:            0
% 2.88/0.99  sat_guarded_non_collapsed_types:        0
% 2.88/0.99  num_pure_diseq_elim:                    0
% 2.88/0.99  simp_replaced_by:                       0
% 2.88/0.99  res_preprocessed:                       98
% 2.88/0.99  prep_upred:                             0
% 2.88/0.99  prep_unflattend:                        160
% 2.88/0.99  smt_new_axioms:                         0
% 2.88/0.99  pred_elim_cands:                        5
% 2.88/0.99  pred_elim:                              2
% 2.88/0.99  pred_elim_cl:                           3
% 2.88/0.99  pred_elim_cycles:                       8
% 2.88/0.99  merged_defs:                            0
% 2.88/0.99  merged_defs_ncl:                        0
% 2.88/0.99  bin_hyper_res:                          0
% 2.88/0.99  prep_cycles:                            4
% 2.88/0.99  pred_elim_time:                         0.034
% 2.88/0.99  splitting_time:                         0.
% 2.88/0.99  sem_filter_time:                        0.
% 2.88/0.99  monotx_time:                            0.
% 2.88/0.99  subtype_inf_time:                       0.
% 2.88/0.99  
% 2.88/0.99  ------ Problem properties
% 2.88/0.99  
% 2.88/0.99  clauses:                                18
% 2.88/0.99  conjectures:                            2
% 2.88/0.99  epr:                                    0
% 2.88/0.99  horn:                                   10
% 2.88/0.99  ground:                                 6
% 2.88/0.99  unary:                                  3
% 2.88/0.99  binary:                                 1
% 2.88/0.99  lits:                                   55
% 2.88/0.99  lits_eq:                                5
% 2.88/0.99  fd_pure:                                0
% 2.88/0.99  fd_pseudo:                              0
% 2.88/0.99  fd_cond:                                0
% 2.88/0.99  fd_pseudo_cond:                         2
% 2.88/0.99  ac_symbols:                             0
% 2.88/0.99  
% 2.88/0.99  ------ Propositional Solver
% 2.88/0.99  
% 2.88/0.99  prop_solver_calls:                      29
% 2.88/0.99  prop_fast_solver_calls:                 1567
% 2.88/0.99  smt_solver_calls:                       0
% 2.88/0.99  smt_fast_solver_calls:                  0
% 2.88/0.99  prop_num_of_clauses:                    3176
% 2.88/0.99  prop_preprocess_simplified:             7176
% 2.88/0.99  prop_fo_subsumed:                       74
% 2.88/0.99  prop_solver_time:                       0.
% 2.88/0.99  smt_solver_time:                        0.
% 2.88/0.99  smt_fast_solver_time:                   0.
% 2.88/0.99  prop_fast_solver_time:                  0.
% 2.88/0.99  prop_unsat_core_time:                   0.
% 2.88/0.99  
% 2.88/0.99  ------ QBF
% 2.88/0.99  
% 2.88/0.99  qbf_q_res:                              0
% 2.88/0.99  qbf_num_tautologies:                    0
% 2.88/0.99  qbf_prep_cycles:                        0
% 2.88/0.99  
% 2.88/0.99  ------ BMC1
% 2.88/0.99  
% 2.88/0.99  bmc1_current_bound:                     -1
% 2.88/0.99  bmc1_last_solved_bound:                 -1
% 2.88/0.99  bmc1_unsat_core_size:                   -1
% 2.88/0.99  bmc1_unsat_core_parents_size:           -1
% 2.88/0.99  bmc1_merge_next_fun:                    0
% 2.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation
% 2.88/0.99  
% 2.88/0.99  inst_num_of_clauses:                    816
% 2.88/0.99  inst_num_in_passive:                    204
% 2.88/0.99  inst_num_in_active:                     338
% 2.88/0.99  inst_num_in_unprocessed:                275
% 2.88/0.99  inst_num_of_loops:                      440
% 2.88/0.99  inst_num_of_learning_restarts:          0
% 2.88/0.99  inst_num_moves_active_passive:          99
% 2.88/0.99  inst_lit_activity:                      0
% 2.88/0.99  inst_lit_activity_moves:                0
% 2.88/0.99  inst_num_tautologies:                   0
% 2.88/0.99  inst_num_prop_implied:                  0
% 2.88/0.99  inst_num_existing_simplified:           0
% 2.88/0.99  inst_num_eq_res_simplified:             0
% 2.88/0.99  inst_num_child_elim:                    0
% 2.88/0.99  inst_num_of_dismatching_blockings:      347
% 2.88/0.99  inst_num_of_non_proper_insts:           899
% 2.88/0.99  inst_num_of_duplicates:                 0
% 2.88/0.99  inst_inst_num_from_inst_to_res:         0
% 2.88/0.99  inst_dismatching_checking_time:         0.
% 2.88/0.99  
% 2.88/0.99  ------ Resolution
% 2.88/0.99  
% 2.88/0.99  res_num_of_clauses:                     0
% 2.88/0.99  res_num_in_passive:                     0
% 2.88/0.99  res_num_in_active:                      0
% 2.88/0.99  res_num_of_loops:                       102
% 2.88/0.99  res_forward_subset_subsumed:            41
% 2.88/0.99  res_backward_subset_subsumed:           2
% 2.88/0.99  res_forward_subsumed:                   0
% 2.88/0.99  res_backward_subsumed:                  0
% 2.88/0.99  res_forward_subsumption_resolution:     3
% 2.88/0.99  res_backward_subsumption_resolution:    0
% 2.88/0.99  res_clause_to_clause_subsumption:       639
% 2.88/0.99  res_orphan_elimination:                 0
% 2.88/0.99  res_tautology_del:                      58
% 2.88/0.99  res_num_eq_res_simplified:              0
% 2.88/0.99  res_num_sel_changes:                    0
% 2.88/0.99  res_moves_from_active_to_pass:          0
% 2.88/0.99  
% 2.88/0.99  ------ Superposition
% 2.88/0.99  
% 2.88/0.99  sup_time_total:                         0.
% 2.88/0.99  sup_time_generating:                    0.
% 2.88/0.99  sup_time_sim_full:                      0.
% 2.88/0.99  sup_time_sim_immed:                     0.
% 2.88/0.99  
% 2.88/0.99  sup_num_of_clauses:                     118
% 2.88/0.99  sup_num_in_active:                      78
% 2.88/0.99  sup_num_in_passive:                     40
% 2.88/0.99  sup_num_of_loops:                       87
% 2.88/0.99  sup_fw_superposition:                   64
% 2.88/0.99  sup_bw_superposition:                   95
% 2.88/0.99  sup_immediate_simplified:               36
% 2.88/0.99  sup_given_eliminated:                   0
% 2.88/0.99  comparisons_done:                       0
% 2.88/0.99  comparisons_avoided:                    6
% 2.88/0.99  
% 2.88/0.99  ------ Simplifications
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  sim_fw_subset_subsumed:                 7
% 2.88/0.99  sim_bw_subset_subsumed:                 18
% 2.88/0.99  sim_fw_subsumed:                        24
% 2.88/0.99  sim_bw_subsumed:                        0
% 2.88/0.99  sim_fw_subsumption_res:                 3
% 2.88/0.99  sim_bw_subsumption_res:                 2
% 2.88/0.99  sim_tautology_del:                      2
% 2.88/0.99  sim_eq_tautology_del:                   1
% 2.88/0.99  sim_eq_res_simp:                        0
% 2.88/0.99  sim_fw_demodulated:                     0
% 2.88/0.99  sim_bw_demodulated:                     2
% 2.88/0.99  sim_light_normalised:                   14
% 2.88/0.99  sim_joinable_taut:                      0
% 2.88/0.99  sim_joinable_simp:                      0
% 2.88/0.99  sim_ac_normalised:                      0
% 2.88/0.99  sim_smt_subsumption:                    0
% 2.88/0.99  
%------------------------------------------------------------------------------
