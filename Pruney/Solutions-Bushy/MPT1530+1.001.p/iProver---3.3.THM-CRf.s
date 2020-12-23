%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1530+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:47 EST 2020

% Result     : Theorem 19.34s
% Output     : CNFRefutation 19.34s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3002)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f68,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) )
                       => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) ) )
                      & ( ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) )
                       => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f13,f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( sP1(X1,X3,X2,X0)
            | ( ( ~ r1_orders_2(X0,X3,X1)
                | ~ r1_orders_2(X0,X2,X1) )
              & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
            | sP0(X1,X3,X2,X0)
            | ( ( ~ r1_orders_2(X0,X1,X3)
                | ~ r1_orders_2(X0,X1,X2) )
              & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( sP1(X1,sK8,X2,X0)
          | ( ( ~ r1_orders_2(X0,sK8,X1)
              | ~ r1_orders_2(X0,X2,X1) )
            & r2_lattice3(X0,k2_tarski(X2,sK8),X1) )
          | sP0(X1,sK8,X2,X0)
          | ( ( ~ r1_orders_2(X0,X1,sK8)
              | ~ r1_orders_2(X0,X1,X2) )
            & r1_lattice3(X0,k2_tarski(X2,sK8),X1) ) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X1,X3,X2,X0)
                | ( ( ~ r1_orders_2(X0,X3,X1)
                    | ~ r1_orders_2(X0,X2,X1) )
                  & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                | sP0(X1,X3,X2,X0)
                | ( ( ~ r1_orders_2(X0,X1,X3)
                    | ~ r1_orders_2(X0,X1,X2) )
                  & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( sP1(X1,X3,sK7,X0)
              | ( ( ~ r1_orders_2(X0,X3,X1)
                  | ~ r1_orders_2(X0,sK7,X1) )
                & r2_lattice3(X0,k2_tarski(sK7,X3),X1) )
              | sP0(X1,X3,sK7,X0)
              | ( ( ~ r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X1,sK7) )
                & r1_lattice3(X0,k2_tarski(sK7,X3),X1) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( sP1(sK6,X3,X2,X0)
                  | ( ( ~ r1_orders_2(X0,X3,sK6)
                      | ~ r1_orders_2(X0,X2,sK6) )
                    & r2_lattice3(X0,k2_tarski(X2,X3),sK6) )
                  | sP0(sK6,X3,X2,X0)
                  | ( ( ~ r1_orders_2(X0,sK6,X3)
                      | ~ r1_orders_2(X0,sK6,X2) )
                    & r1_lattice3(X0,k2_tarski(X2,X3),sK6) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( sP1(X1,X3,X2,X0)
                      | ( ( ~ r1_orders_2(X0,X3,X1)
                          | ~ r1_orders_2(X0,X2,X1) )
                        & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      | sP0(X1,X3,X2,X0)
                      | ( ( ~ r1_orders_2(X0,X1,X3)
                          | ~ r1_orders_2(X0,X1,X2) )
                        & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,sK5)
                    | ( ( ~ r1_orders_2(sK5,X3,X1)
                        | ~ r1_orders_2(sK5,X2,X1) )
                      & r2_lattice3(sK5,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,sK5)
                    | ( ( ~ r1_orders_2(sK5,X1,X3)
                        | ~ r1_orders_2(sK5,X1,X2) )
                      & r1_lattice3(sK5,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( sP1(sK6,sK8,sK7,sK5)
      | ( ( ~ r1_orders_2(sK5,sK8,sK6)
          | ~ r1_orders_2(sK5,sK7,sK6) )
        & r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) )
      | sP0(sK6,sK8,sK7,sK5)
      | ( ( ~ r1_orders_2(sK5,sK6,sK8)
          | ~ r1_orders_2(sK5,sK6,sK7) )
        & r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ) )
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f14,f35,f34,f33,f32])).

fof(f58,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f66,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f65])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X0,X1)
        & r1_orders_2(X3,X0,X2) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f28,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X1,X0)
        & r1_orders_2(X3,X2,X0) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,
    ( sP1(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | sP0(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_orders_2(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X3,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,
    ( sP1(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sP0(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_orders_2(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X3,X0,X1)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( sP1(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sP0(sK6,sK8,sK7,sK5)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X3,X0,X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X3,X2,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,
    ( sP1(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | sP0(sK6,sK8,sK7,sK5)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6266,plain,
    ( r2_hidden(sK7,k2_tarski(sK7,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_78010,plain,
    ( r2_hidden(sK7,k2_tarski(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6266])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5619,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_390,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_391,plain,
    ( r1_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_5613,plain,
    ( r1_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5624,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_339,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_340,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK4(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_5616,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5622,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7578,plain,
    ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
    | sK4(sK5,k2_tarski(X0,X1),X2) = X1
    | r2_lattice3(sK5,k2_tarski(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5616,c_5622])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_303,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_304,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_5618,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_8646,plain,
    ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
    | sK4(sK5,k2_tarski(X0,X1),X2) = X1
    | r1_orders_2(sK5,X3,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7578,c_5618])).

cnf(c_11945,plain,
    ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
    | sK4(sK5,k2_tarski(X0,X1),X2) = X1
    | r1_orders_2(sK5,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_8646])).

cnf(c_14417,plain,
    ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X0
    | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X1
    | r1_orders_2(sK5,X1,sK3(sK5,X2,X3)) = iProver_top
    | r1_lattice3(sK5,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5613,c_11945])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_420,plain,
    ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_421,plain,
    ( ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
    | r1_lattice3(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_5611,plain,
    ( r1_orders_2(sK5,X0,sK3(sK5,X1,X0)) != iProver_top
    | r1_lattice3(sK5,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_20118,plain,
    ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X1)) = X0
    | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X1)) = X1
    | r1_lattice3(sK5,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14417,c_5611])).

cnf(c_20351,plain,
    ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,X1,sK6)) = X0
    | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,X1,sK6)) = sK6
    | r1_lattice3(sK5,X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_20118])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_lattice3(X3,k2_tarski(X2,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r2_lattice3(X3,k2_tarski(X2,X1),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( sP0(sK6,sK8,sK7,sK5)
    | sP1(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1097,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_1098,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_1582,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1098])).

cnf(c_1583,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1582])).

cnf(c_5604,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_8645,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7578,c_5604])).

cnf(c_29,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_369,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_370,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r1_lattice3(sK5,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_5970,plain,
    ( r1_orders_2(sK5,X0,sK8)
    | ~ r1_lattice3(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ r2_hidden(sK8,X1) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_6542,plain,
    ( r1_orders_2(sK5,X0,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(X1,sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ r2_hidden(sK8,k2_tarski(X1,sK8)) ),
    inference(instantiation,[status(thm)],[c_5970])).

cnf(c_6989,plain,
    ( r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(X0,sK8),sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK8,k2_tarski(X0,sK8)) ),
    inference(instantiation,[status(thm)],[c_6542])).

cnf(c_8864,plain,
    ( r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK8,k2_tarski(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6989])).

cnf(c_8865,plain,
    ( r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8864])).

cnf(c_6228,plain,
    ( r2_hidden(sK8,k2_tarski(X0,sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10304,plain,
    ( r2_hidden(sK8,k2_tarski(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6228])).

cnf(c_10305,plain,
    ( r2_hidden(sK8,k2_tarski(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10304])).

cnf(c_13248,plain,
    ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8645,c_29,c_31,c_8865,c_10305])).

cnf(c_13249,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_13248])).

cnf(c_21076,plain,
    ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
    | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20351,c_13249])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_75,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_78,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_405,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_406,plain,
    ( r1_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK3(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_2520,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(sK3(sK5,X1,X0),X1)
    | k2_tarski(sK7,sK8) != X1
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1583,c_406])).

cnf(c_2521,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_2520])).

cnf(c_2522,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2521])).

cnf(c_2618,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_tarski(sK7,sK8) != X1
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1583,c_421])).

cnf(c_2619,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_2618])).

cnf(c_2620,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_5151,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6220,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_5151])).

cnf(c_5157,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_11130,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | X0 != sK5
    | X2 != sK8
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_5157])).

cnf(c_23332,plain,
    ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK8)
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK8
    | sK5 != sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_11130])).

cnf(c_23348,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK8
    | sK5 != sK5
    | sK6 != sK6
    | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23332])).

cnf(c_11135,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | X0 != sK5
    | X2 != sK7
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_5157])).

cnf(c_23331,plain,
    ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK7)
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK7
    | sK5 != sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_11135])).

cnf(c_23350,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK7
    | sK5 != sK5
    | sK6 != sK6
    | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23331])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_orders_2(X3,X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( sP0(sK6,sK8,sK7,sK5)
    | sP1(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1051,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | sK5 != X0
    | sK7 != X3
    | sK8 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_1052,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(unflattening,[status(thm)],[c_1051])).

cnf(c_1606,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1052])).

cnf(c_1607,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1606])).

cnf(c_5603,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1607])).

cnf(c_21077,plain,
    ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
    | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_20351,c_5603])).

cnf(c_2595,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
    | r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_tarski(sK7,sK8) != X1
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1607,c_421])).

cnf(c_2596,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_2595])).

cnf(c_2597,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2596])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_orders_2(X3,X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( sP0(sK6,sK8,sK7,sK5)
    | sP1(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1035,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X3
    | sK8 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_1036,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1035])).

cnf(c_1548,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X3
    | sK8 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1036])).

cnf(c_1549,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1548])).

cnf(c_5606,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_8341,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5606,c_5618])).

cnf(c_2970,plain,
    ( r1_orders_2(sK5,X0,X1)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2)
    | k2_tarski(sK7,sK8) != X2
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1549,c_304])).

cnf(c_2971,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_2970])).

cnf(c_2972,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2971])).

cnf(c_12299,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8341,c_29,c_31,c_2972,c_8865,c_10305])).

cnf(c_12300,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12299])).

cnf(c_12311,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_12300])).

cnf(c_12481,plain,
    ( r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12311,c_31])).

cnf(c_12482,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_12481])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_orders_2(X3,X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1491,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X2
    | sK8 != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1036])).

cnf(c_1492,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1491])).

cnf(c_5609,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_9397,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5609,c_5618])).

cnf(c_3030,plain,
    ( r1_orders_2(sK5,X0,X1)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2)
    | k2_tarski(sK7,sK8) != X2
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1492,c_304])).

cnf(c_3031,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_3030])).

cnf(c_3035,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,X0,sK6)
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3031,c_26])).

cnf(c_3036,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(renaming,[status(thm)],[c_3035])).

cnf(c_3037,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3036])).

cnf(c_12605,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9397,c_3037])).

cnf(c_12606,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12605])).

cnf(c_12618,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5616,c_12606])).

cnf(c_12616,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_12606])).

cnf(c_13124,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12618,c_31,c_12616])).

cnf(c_5620,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5614,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | r1_lattice3(sK5,X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_6017,plain,
    ( r1_orders_2(sK5,X0,sK7) = iProver_top
    | r1_lattice3(sK5,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5620,c_5614])).

cnf(c_6493,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,X0,sK6) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_6017])).

cnf(c_13134,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13124,c_6493])).

cnf(c_5623,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13245,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13134,c_5623])).

cnf(c_5612,plain,
    ( r1_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_7389,plain,
    ( sK3(sK5,k2_tarski(X0,X1),X2) = X0
    | sK3(sK5,k2_tarski(X0,X1),X2) = X1
    | r1_lattice3(sK5,k2_tarski(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5612,c_5622])).

cnf(c_8482,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7389,c_5603])).

cnf(c_12392,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8482,c_29,c_31,c_12311])).

cnf(c_12404,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12392,c_5618])).

cnf(c_12967,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12404,c_29])).

cnf(c_12968,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12967])).

cnf(c_12983,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5616,c_12968])).

cnf(c_12981,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_12968])).

cnf(c_13662,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12983,c_31,c_12981,c_13245])).

cnf(c_13663,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_13662])).

cnf(c_27101,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21077,c_29,c_75,c_78,c_2597,c_6220,c_12482,c_13245,c_13663,c_23348,c_23350])).

cnf(c_27110,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27101,c_5618])).

cnf(c_27425,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27110,c_29])).

cnf(c_27426,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_27425])).

cnf(c_27436,plain,
    ( r1_orders_2(sK5,sK8,sK6) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_27426])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2,X3)
    | r1_orders_2(X3,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1012,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_1013,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1627,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1013])).

cnf(c_1628,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1627])).

cnf(c_5602,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1628])).

cnf(c_21078,plain,
    ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
    | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_20351,c_5602])).

cnf(c_2572,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k2_tarski(sK7,sK8) != X1
    | sK5 != sK5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1628,c_421])).

cnf(c_2573,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_2572])).

cnf(c_2575,plain,
    ( ~ r1_orders_2(sK5,sK6,sK8)
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | r1_orders_2(sK5,sK7,sK6)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2573,c_26])).

cnf(c_2576,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | ~ r1_orders_2(sK5,sK6,sK7)
    | ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(renaming,[status(thm)],[c_2575])).

cnf(c_2577,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_996,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_997,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_1566,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X3
    | sK8 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_997])).

cnf(c_1567,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1566])).

cnf(c_5605,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_8319,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5605,c_5618])).

cnf(c_2940,plain,
    ( r1_orders_2(sK5,X0,X1)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2)
    | k2_tarski(sK7,sK8) != X2
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1567,c_304])).

cnf(c_2941,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_2940])).

cnf(c_2945,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,X0,sK6)
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_26])).

cnf(c_2946,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(renaming,[status(thm)],[c_2945])).

cnf(c_2947,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2946])).

cnf(c_12219,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8319,c_29,c_31,c_2947,c_8865,c_10305])).

cnf(c_12220,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12219])).

cnf(c_12232,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_12220])).

cnf(c_12425,plain,
    ( r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12232,c_30])).

cnf(c_12426,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_12425])).

cnf(c_1509,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X2
    | sK8 != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_997])).

cnf(c_1510,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1509])).

cnf(c_5608,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_9375,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5608,c_5618])).

cnf(c_3000,plain,
    ( r1_orders_2(sK5,X0,X1)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2)
    | k2_tarski(sK7,sK8) != X2
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1510,c_304])).

cnf(c_3001,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_3000])).

cnf(c_3005,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,X0,sK6)
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3001,c_26])).

cnf(c_3006,plain,
    ( r1_orders_2(sK5,X0,sK6)
    | r1_orders_2(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
    inference(renaming,[status(thm)],[c_3005])).

cnf(c_3007,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3006])).

cnf(c_12506,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9375,c_29,c_3002])).

cnf(c_12507,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12506])).

cnf(c_12519,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5616,c_12507])).

cnf(c_12518,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_12507])).

cnf(c_13069,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12519,c_30,c_12518])).

cnf(c_13079,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13069,c_6493])).

cnf(c_13116,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13079,c_5623])).

cnf(c_8483,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7389,c_5602])).

cnf(c_12810,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8483,c_29,c_30,c_12232])).

cnf(c_12822,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12810,c_5618])).

cnf(c_13386,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12822,c_29,c_13116])).

cnf(c_13387,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13386])).

cnf(c_13400,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_13387])).

cnf(c_28013,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21078,c_30,c_75,c_78,c_2577,c_6220,c_12426,c_13116,c_13400,c_23348,c_23350])).

cnf(c_28022,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28013,c_5618])).

cnf(c_28172,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | r1_orders_2(sK5,X0,sK6) = iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28022,c_29])).

cnf(c_28173,plain,
    ( r1_orders_2(sK5,X0,sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_28172])).

cnf(c_28184,plain,
    ( r1_orders_2(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_28173])).

cnf(c_21,negated_conjecture,
    ( sP0(sK6,sK8,sK7,sK5)
    | sP1(sK6,sK8,sK7,sK5)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1078,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X1
    | sK8 != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_1079,plain,
    ( sP0(sK6,sK8,sK7,sK5)
    | ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_1527,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X3
    | sK8 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1079])).

cnf(c_1528,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1527])).

cnf(c_5607,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_9783,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7578,c_5607])).

cnf(c_1470,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK5 != X0
    | sK7 != X2
    | sK8 != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1079])).

cnf(c_1471,plain,
    ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(unflattening,[status(thm)],[c_1470])).

cnf(c_5610,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_9809,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7578,c_5610])).

cnf(c_13258,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7389,c_13249])).

cnf(c_5946,plain,
    ( ~ r1_orders_2(sK5,sK6,sK3(sK5,X0,sK6))
    | r1_lattice3(sK5,X0,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_8868,plain,
    ( ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(X0,sK8),sK6))
    | r1_lattice3(sK5,k2_tarski(X0,sK8),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5946])).

cnf(c_16721,plain,
    ( ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8868])).

cnf(c_16722,plain,
    ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16721])).

cnf(c_35052,plain,
    ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9783,c_29,c_30,c_31,c_75,c_78,c_6220,c_9809,c_13258,c_16722,c_23348,c_23350,c_27436,c_28184])).

cnf(c_35053,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_35052])).

cnf(c_35061,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35053,c_6493])).

cnf(c_5975,plain,
    ( r1_orders_2(sK5,X0,sK7)
    | ~ r1_lattice3(sK5,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,X1) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_6563,plain,
    ( r1_orders_2(sK5,X0,sK7)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,k2_tarski(sK7,X1)) ),
    inference(instantiation,[status(thm)],[c_5975])).

cnf(c_7034,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,X0),sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,k2_tarski(sK7,X0)) ),
    inference(instantiation,[status(thm)],[c_6563])).

cnf(c_9341,plain,
    ( r1_orders_2(sK5,sK6,sK7)
    | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK7,k2_tarski(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_7034])).

cnf(c_9342,plain,
    ( r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9341])).

cnf(c_35059,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_35053,c_13249])).

cnf(c_35308,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35061,c_30,c_31,c_27436,c_28184,c_35059])).

cnf(c_35309,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_35308])).

cnf(c_35315,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35309,c_5623])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_354,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_355,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_5615,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_35339,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35315,c_5615])).

cnf(c_35759,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35339,c_29,c_30,c_28184])).

cnf(c_6192,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK7,X1))
    | X0 = X1
    | X0 = sK7 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6665,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK7,sK8))
    | X0 = sK7
    | X0 = sK8 ),
    inference(instantiation,[status(thm)],[c_6192])).

cnf(c_39598,plain,
    ( ~ r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8))
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
    inference(instantiation,[status(thm)],[c_6665])).

cnf(c_39607,plain,
    ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
    | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39598])).

cnf(c_11946,plain,
    ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
    | sK4(sK5,k2_tarski(X0,X1),X2) = X1
    | r1_orders_2(sK5,X0,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5623,c_8646])).

cnf(c_16139,plain,
    ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X0
    | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X1
    | r1_orders_2(sK5,X0,sK3(sK5,X2,X3)) = iProver_top
    | r1_lattice3(sK5,X2,X3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5613,c_11946])).

cnf(c_23944,plain,
    ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X0)) = X0
    | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X0)) = X1
    | r1_lattice3(sK5,X2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16139,c_5611])).

cnf(c_24066,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,X1,sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,X1,sK6)) = sK6
    | r1_lattice3(sK5,X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_23944])).

cnf(c_7586,plain,
    ( r1_orders_2(sK5,X0,sK3(sK5,X1,X2)) = iProver_top
    | r1_lattice3(sK5,X3,X0) != iProver_top
    | r1_lattice3(sK5,X1,X2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X1,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5613,c_5614])).

cnf(c_10403,plain,
    ( r1_orders_2(sK5,X0,sK3(sK5,X1,X2)) = iProver_top
    | r1_lattice3(sK5,X1,X2) = iProver_top
    | r1_lattice3(sK5,k2_tarski(X3,sK3(sK5,X1,X2)),X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_7586])).

cnf(c_24409,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
    | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
    | r1_lattice3(sK5,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24066,c_10403])).

cnf(c_39991,plain,
    ( m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
    | r1_lattice3(sK5,X2,X3) = iProver_top
    | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24409,c_29])).

cnf(c_39992,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
    | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
    | r1_lattice3(sK5,X2,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_39991])).

cnf(c_40002,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
    | r1_lattice3(sK5,X2,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39992,c_5611])).

cnf(c_40007,plain,
    ( r1_lattice3(sK5,X2,sK6) = iProver_top
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40002,c_29])).

cnf(c_40008,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
    | r1_lattice3(sK5,X2,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_40007])).

cnf(c_5621,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6016,plain,
    ( r1_orders_2(sK5,X0,sK8) = iProver_top
    | r1_lattice3(sK5,X1,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5621,c_5614])).

cnf(c_6082,plain,
    ( r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,X0,sK6) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_6016])).

cnf(c_40018,plain,
    ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
    | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r2_hidden(sK8,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_40008,c_6082])).

cnf(c_3138,plain,
    ( ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_tarski(sK7,sK8) != X0
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1528,c_355])).

cnf(c_3139,plain,
    ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_3138])).

cnf(c_3141,plain,
    ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3139,c_26])).

cnf(c_3142,plain,
    ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK8)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
    inference(renaming,[status(thm)],[c_3141])).

cnf(c_3143,plain,
    ( r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) != iProver_top
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3142])).

cnf(c_35766,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK8) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_35759,c_5607])).

cnf(c_11081,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | X0 != sK5
    | X1 != sK8
    | X2 != sK6 ),
    inference(instantiation,[status(thm)],[c_5157])).

cnf(c_37632,plain,
    ( r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) != sK8
    | sK5 != sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_11081])).

cnf(c_37639,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) != sK8
    | sK5 != sK5
    | sK6 != sK6
    | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) = iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37632])).

cnf(c_40537,plain,
    ( r1_orders_2(sK5,sK6,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40018,c_29,c_30,c_31,c_75,c_78,c_3143,c_6220,c_8865,c_10305,c_27436,c_28184,c_35766,c_37639])).

cnf(c_41936,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21076,c_29,c_30,c_31,c_75,c_78,c_2522,c_2620,c_3143,c_6220,c_8865,c_10305,c_23348,c_23350,c_27436,c_28184,c_35339,c_35766,c_37639,c_39607])).

cnf(c_5916,plain,
    ( r2_lattice3(sK5,X0,sK6)
    | ~ r1_orders_2(sK5,sK4(sK5,X0,sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_8274,plain,
    ( r2_lattice3(sK5,k2_tarski(X0,sK8),sK6)
    | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(X0,sK8),sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5916])).

cnf(c_12211,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8274])).

cnf(c_12212,plain,
    ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12211])).

cnf(c_41940,plain,
    ( r1_orders_2(sK5,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41936,c_29,c_30,c_31,c_75,c_78,c_2522,c_2620,c_3143,c_6220,c_8865,c_10305,c_12212,c_23348,c_23350,c_27436,c_28184,c_35766,c_37639,c_39607])).

cnf(c_41942,plain,
    ( ~ r1_orders_2(sK5,sK6,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_41940])).

cnf(c_35765,plain,
    ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
    | r1_orders_2(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK8,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK7) = iProver_top
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_35759,c_5610])).

cnf(c_35811,plain,
    ( ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_35765])).

cnf(c_28226,plain,
    ( r1_orders_2(sK5,sK7,sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_28184])).

cnf(c_27485,plain,
    ( r1_orders_2(sK5,sK8,sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27436])).

cnf(c_3207,plain,
    ( ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k2_tarski(sK7,sK8) != X0
    | sK5 != sK5
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1471,c_355])).

cnf(c_3208,plain,
    ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
    | ~ r1_orders_2(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK8,sK6)
    | r1_orders_2(sK5,sK6,sK7)
    | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_3207])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78010,c_41942,c_37632,c_35811,c_28226,c_27485,c_9341,c_6220,c_3208,c_78,c_75,c_24,c_25,c_26])).


%------------------------------------------------------------------------------
