%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:27 EST 2020

% Result     : Theorem 23.98s
% Output     : CNFRefutation 23.98s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.98/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.98/3.50  
% 23.98/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.98/3.50  
% 23.98/3.50  ------  iProver source info
% 23.98/3.50  
% 23.98/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.98/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.98/3.50  git: non_committed_changes: false
% 23.98/3.50  git: last_make_outside_of_git: false
% 23.98/3.50  
% 23.98/3.50  ------ 
% 23.98/3.50  
% 23.98/3.50  ------ Input Options
% 23.98/3.50  
% 23.98/3.50  --out_options                           all
% 23.98/3.50  --tptp_safe_out                         true
% 23.98/3.50  --problem_path                          ""
% 23.98/3.50  --include_path                          ""
% 23.98/3.50  --clausifier                            res/vclausify_rel
% 23.98/3.50  --clausifier_options                    --mode clausify
% 23.98/3.50  --stdin                                 false
% 23.98/3.50  --stats_out                             all
% 23.98/3.50  
% 23.98/3.50  ------ General Options
% 23.98/3.50  
% 23.98/3.50  --fof                                   false
% 23.98/3.50  --time_out_real                         305.
% 23.98/3.50  --time_out_virtual                      -1.
% 23.98/3.50  --symbol_type_check                     false
% 23.98/3.50  --clausify_out                          false
% 23.98/3.50  --sig_cnt_out                           false
% 23.98/3.50  --trig_cnt_out                          false
% 23.98/3.50  --trig_cnt_out_tolerance                1.
% 23.98/3.50  --trig_cnt_out_sk_spl                   false
% 23.98/3.50  --abstr_cl_out                          false
% 23.98/3.50  
% 23.98/3.50  ------ Global Options
% 23.98/3.50  
% 23.98/3.50  --schedule                              default
% 23.98/3.50  --add_important_lit                     false
% 23.98/3.50  --prop_solver_per_cl                    1000
% 23.98/3.50  --min_unsat_core                        false
% 23.98/3.50  --soft_assumptions                      false
% 23.98/3.50  --soft_lemma_size                       3
% 23.98/3.50  --prop_impl_unit_size                   0
% 23.98/3.50  --prop_impl_unit                        []
% 23.98/3.50  --share_sel_clauses                     true
% 23.98/3.50  --reset_solvers                         false
% 23.98/3.50  --bc_imp_inh                            [conj_cone]
% 23.98/3.50  --conj_cone_tolerance                   3.
% 23.98/3.50  --extra_neg_conj                        none
% 23.98/3.50  --large_theory_mode                     true
% 23.98/3.50  --prolific_symb_bound                   200
% 23.98/3.50  --lt_threshold                          2000
% 23.98/3.50  --clause_weak_htbl                      true
% 23.98/3.50  --gc_record_bc_elim                     false
% 23.98/3.50  
% 23.98/3.50  ------ Preprocessing Options
% 23.98/3.50  
% 23.98/3.50  --preprocessing_flag                    true
% 23.98/3.50  --time_out_prep_mult                    0.1
% 23.98/3.50  --splitting_mode                        input
% 23.98/3.50  --splitting_grd                         true
% 23.98/3.50  --splitting_cvd                         false
% 23.98/3.50  --splitting_cvd_svl                     false
% 23.98/3.50  --splitting_nvd                         32
% 23.98/3.50  --sub_typing                            true
% 23.98/3.50  --prep_gs_sim                           true
% 23.98/3.50  --prep_unflatten                        true
% 23.98/3.50  --prep_res_sim                          true
% 23.98/3.50  --prep_upred                            true
% 23.98/3.50  --prep_sem_filter                       exhaustive
% 23.98/3.50  --prep_sem_filter_out                   false
% 23.98/3.50  --pred_elim                             true
% 23.98/3.50  --res_sim_input                         true
% 23.98/3.50  --eq_ax_congr_red                       true
% 23.98/3.50  --pure_diseq_elim                       true
% 23.98/3.50  --brand_transform                       false
% 23.98/3.50  --non_eq_to_eq                          false
% 23.98/3.50  --prep_def_merge                        true
% 23.98/3.50  --prep_def_merge_prop_impl              false
% 23.98/3.50  --prep_def_merge_mbd                    true
% 23.98/3.50  --prep_def_merge_tr_red                 false
% 23.98/3.50  --prep_def_merge_tr_cl                  false
% 23.98/3.50  --smt_preprocessing                     true
% 23.98/3.50  --smt_ac_axioms                         fast
% 23.98/3.50  --preprocessed_out                      false
% 23.98/3.50  --preprocessed_stats                    false
% 23.98/3.50  
% 23.98/3.50  ------ Abstraction refinement Options
% 23.98/3.50  
% 23.98/3.50  --abstr_ref                             []
% 23.98/3.50  --abstr_ref_prep                        false
% 23.98/3.50  --abstr_ref_until_sat                   false
% 23.98/3.50  --abstr_ref_sig_restrict                funpre
% 23.98/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.98/3.50  --abstr_ref_under                       []
% 23.98/3.50  
% 23.98/3.50  ------ SAT Options
% 23.98/3.50  
% 23.98/3.50  --sat_mode                              false
% 23.98/3.50  --sat_fm_restart_options                ""
% 23.98/3.50  --sat_gr_def                            false
% 23.98/3.50  --sat_epr_types                         true
% 23.98/3.50  --sat_non_cyclic_types                  false
% 23.98/3.50  --sat_finite_models                     false
% 23.98/3.50  --sat_fm_lemmas                         false
% 23.98/3.50  --sat_fm_prep                           false
% 23.98/3.50  --sat_fm_uc_incr                        true
% 23.98/3.50  --sat_out_model                         small
% 23.98/3.50  --sat_out_clauses                       false
% 23.98/3.50  
% 23.98/3.50  ------ QBF Options
% 23.98/3.50  
% 23.98/3.50  --qbf_mode                              false
% 23.98/3.50  --qbf_elim_univ                         false
% 23.98/3.50  --qbf_dom_inst                          none
% 23.98/3.50  --qbf_dom_pre_inst                      false
% 23.98/3.50  --qbf_sk_in                             false
% 23.98/3.50  --qbf_pred_elim                         true
% 23.98/3.50  --qbf_split                             512
% 23.98/3.50  
% 23.98/3.50  ------ BMC1 Options
% 23.98/3.50  
% 23.98/3.50  --bmc1_incremental                      false
% 23.98/3.50  --bmc1_axioms                           reachable_all
% 23.98/3.50  --bmc1_min_bound                        0
% 23.98/3.50  --bmc1_max_bound                        -1
% 23.98/3.50  --bmc1_max_bound_default                -1
% 23.98/3.50  --bmc1_symbol_reachability              true
% 23.98/3.50  --bmc1_property_lemmas                  false
% 23.98/3.50  --bmc1_k_induction                      false
% 23.98/3.50  --bmc1_non_equiv_states                 false
% 23.98/3.50  --bmc1_deadlock                         false
% 23.98/3.50  --bmc1_ucm                              false
% 23.98/3.50  --bmc1_add_unsat_core                   none
% 23.98/3.50  --bmc1_unsat_core_children              false
% 23.98/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.98/3.50  --bmc1_out_stat                         full
% 23.98/3.50  --bmc1_ground_init                      false
% 23.98/3.50  --bmc1_pre_inst_next_state              false
% 23.98/3.50  --bmc1_pre_inst_state                   false
% 23.98/3.50  --bmc1_pre_inst_reach_state             false
% 23.98/3.50  --bmc1_out_unsat_core                   false
% 23.98/3.50  --bmc1_aig_witness_out                  false
% 23.98/3.50  --bmc1_verbose                          false
% 23.98/3.50  --bmc1_dump_clauses_tptp                false
% 23.98/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.98/3.50  --bmc1_dump_file                        -
% 23.98/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.98/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.98/3.50  --bmc1_ucm_extend_mode                  1
% 23.98/3.50  --bmc1_ucm_init_mode                    2
% 23.98/3.50  --bmc1_ucm_cone_mode                    none
% 23.98/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.98/3.50  --bmc1_ucm_relax_model                  4
% 23.98/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.98/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.98/3.50  --bmc1_ucm_layered_model                none
% 23.98/3.50  --bmc1_ucm_max_lemma_size               10
% 23.98/3.50  
% 23.98/3.50  ------ AIG Options
% 23.98/3.50  
% 23.98/3.50  --aig_mode                              false
% 23.98/3.50  
% 23.98/3.50  ------ Instantiation Options
% 23.98/3.50  
% 23.98/3.50  --instantiation_flag                    true
% 23.98/3.50  --inst_sos_flag                         false
% 23.98/3.50  --inst_sos_phase                        true
% 23.98/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.98/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.98/3.50  --inst_lit_sel_side                     num_symb
% 23.98/3.50  --inst_solver_per_active                1400
% 23.98/3.50  --inst_solver_calls_frac                1.
% 23.98/3.50  --inst_passive_queue_type               priority_queues
% 23.98/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.98/3.50  --inst_passive_queues_freq              [25;2]
% 23.98/3.50  --inst_dismatching                      true
% 23.98/3.50  --inst_eager_unprocessed_to_passive     true
% 23.98/3.50  --inst_prop_sim_given                   true
% 23.98/3.50  --inst_prop_sim_new                     false
% 23.98/3.50  --inst_subs_new                         false
% 23.98/3.50  --inst_eq_res_simp                      false
% 23.98/3.50  --inst_subs_given                       false
% 23.98/3.50  --inst_orphan_elimination               true
% 23.98/3.50  --inst_learning_loop_flag               true
% 23.98/3.50  --inst_learning_start                   3000
% 23.98/3.50  --inst_learning_factor                  2
% 23.98/3.50  --inst_start_prop_sim_after_learn       3
% 23.98/3.50  --inst_sel_renew                        solver
% 23.98/3.50  --inst_lit_activity_flag                true
% 23.98/3.50  --inst_restr_to_given                   false
% 23.98/3.50  --inst_activity_threshold               500
% 23.98/3.50  --inst_out_proof                        true
% 23.98/3.50  
% 23.98/3.50  ------ Resolution Options
% 23.98/3.50  
% 23.98/3.50  --resolution_flag                       true
% 23.98/3.50  --res_lit_sel                           adaptive
% 23.98/3.50  --res_lit_sel_side                      none
% 23.98/3.50  --res_ordering                          kbo
% 23.98/3.50  --res_to_prop_solver                    active
% 23.98/3.50  --res_prop_simpl_new                    false
% 23.98/3.50  --res_prop_simpl_given                  true
% 23.98/3.50  --res_passive_queue_type                priority_queues
% 23.98/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.98/3.50  --res_passive_queues_freq               [15;5]
% 23.98/3.50  --res_forward_subs                      full
% 23.98/3.50  --res_backward_subs                     full
% 23.98/3.50  --res_forward_subs_resolution           true
% 23.98/3.50  --res_backward_subs_resolution          true
% 23.98/3.50  --res_orphan_elimination                true
% 23.98/3.50  --res_time_limit                        2.
% 23.98/3.50  --res_out_proof                         true
% 23.98/3.50  
% 23.98/3.50  ------ Superposition Options
% 23.98/3.50  
% 23.98/3.50  --superposition_flag                    true
% 23.98/3.50  --sup_passive_queue_type                priority_queues
% 23.98/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.98/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.98/3.50  --demod_completeness_check              fast
% 23.98/3.50  --demod_use_ground                      true
% 23.98/3.50  --sup_to_prop_solver                    passive
% 23.98/3.50  --sup_prop_simpl_new                    true
% 23.98/3.50  --sup_prop_simpl_given                  true
% 23.98/3.50  --sup_fun_splitting                     false
% 23.98/3.50  --sup_smt_interval                      50000
% 23.98/3.50  
% 23.98/3.50  ------ Superposition Simplification Setup
% 23.98/3.50  
% 23.98/3.50  --sup_indices_passive                   []
% 23.98/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.98/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_full_bw                           [BwDemod]
% 23.98/3.50  --sup_immed_triv                        [TrivRules]
% 23.98/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.98/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_immed_bw_main                     []
% 23.98/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.98/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.98/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.98/3.50  
% 23.98/3.50  ------ Combination Options
% 23.98/3.50  
% 23.98/3.50  --comb_res_mult                         3
% 23.98/3.50  --comb_sup_mult                         2
% 23.98/3.50  --comb_inst_mult                        10
% 23.98/3.50  
% 23.98/3.50  ------ Debug Options
% 23.98/3.50  
% 23.98/3.50  --dbg_backtrace                         false
% 23.98/3.50  --dbg_dump_prop_clauses                 false
% 23.98/3.50  --dbg_dump_prop_clauses_file            -
% 23.98/3.50  --dbg_out_stat                          false
% 23.98/3.50  ------ Parsing...
% 23.98/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.98/3.50  
% 23.98/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 23.98/3.50  
% 23.98/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.98/3.50  
% 23.98/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.98/3.50  ------ Proving...
% 23.98/3.50  ------ Problem Properties 
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  clauses                                 26
% 23.98/3.50  conjectures                             3
% 23.98/3.50  EPR                                     0
% 23.98/3.50  Horn                                    12
% 23.98/3.50  unary                                   5
% 23.98/3.50  binary                                  0
% 23.98/3.50  lits                                    88
% 23.98/3.50  lits eq                                 9
% 23.98/3.50  fd_pure                                 0
% 23.98/3.50  fd_pseudo                               0
% 23.98/3.50  fd_cond                                 0
% 23.98/3.50  fd_pseudo_cond                          3
% 23.98/3.50  AC symbols                              0
% 23.98/3.50  
% 23.98/3.50  ------ Schedule dynamic 5 is on 
% 23.98/3.50  
% 23.98/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  ------ 
% 23.98/3.50  Current options:
% 23.98/3.50  ------ 
% 23.98/3.50  
% 23.98/3.50  ------ Input Options
% 23.98/3.50  
% 23.98/3.50  --out_options                           all
% 23.98/3.50  --tptp_safe_out                         true
% 23.98/3.50  --problem_path                          ""
% 23.98/3.50  --include_path                          ""
% 23.98/3.50  --clausifier                            res/vclausify_rel
% 23.98/3.50  --clausifier_options                    --mode clausify
% 23.98/3.50  --stdin                                 false
% 23.98/3.50  --stats_out                             all
% 23.98/3.50  
% 23.98/3.50  ------ General Options
% 23.98/3.50  
% 23.98/3.50  --fof                                   false
% 23.98/3.50  --time_out_real                         305.
% 23.98/3.50  --time_out_virtual                      -1.
% 23.98/3.50  --symbol_type_check                     false
% 23.98/3.50  --clausify_out                          false
% 23.98/3.50  --sig_cnt_out                           false
% 23.98/3.50  --trig_cnt_out                          false
% 23.98/3.50  --trig_cnt_out_tolerance                1.
% 23.98/3.50  --trig_cnt_out_sk_spl                   false
% 23.98/3.50  --abstr_cl_out                          false
% 23.98/3.50  
% 23.98/3.50  ------ Global Options
% 23.98/3.50  
% 23.98/3.50  --schedule                              default
% 23.98/3.50  --add_important_lit                     false
% 23.98/3.50  --prop_solver_per_cl                    1000
% 23.98/3.50  --min_unsat_core                        false
% 23.98/3.50  --soft_assumptions                      false
% 23.98/3.50  --soft_lemma_size                       3
% 23.98/3.50  --prop_impl_unit_size                   0
% 23.98/3.50  --prop_impl_unit                        []
% 23.98/3.50  --share_sel_clauses                     true
% 23.98/3.50  --reset_solvers                         false
% 23.98/3.50  --bc_imp_inh                            [conj_cone]
% 23.98/3.50  --conj_cone_tolerance                   3.
% 23.98/3.50  --extra_neg_conj                        none
% 23.98/3.50  --large_theory_mode                     true
% 23.98/3.50  --prolific_symb_bound                   200
% 23.98/3.50  --lt_threshold                          2000
% 23.98/3.50  --clause_weak_htbl                      true
% 23.98/3.50  --gc_record_bc_elim                     false
% 23.98/3.50  
% 23.98/3.50  ------ Preprocessing Options
% 23.98/3.50  
% 23.98/3.50  --preprocessing_flag                    true
% 23.98/3.50  --time_out_prep_mult                    0.1
% 23.98/3.50  --splitting_mode                        input
% 23.98/3.50  --splitting_grd                         true
% 23.98/3.50  --splitting_cvd                         false
% 23.98/3.50  --splitting_cvd_svl                     false
% 23.98/3.50  --splitting_nvd                         32
% 23.98/3.50  --sub_typing                            true
% 23.98/3.50  --prep_gs_sim                           true
% 23.98/3.50  --prep_unflatten                        true
% 23.98/3.50  --prep_res_sim                          true
% 23.98/3.50  --prep_upred                            true
% 23.98/3.50  --prep_sem_filter                       exhaustive
% 23.98/3.50  --prep_sem_filter_out                   false
% 23.98/3.50  --pred_elim                             true
% 23.98/3.50  --res_sim_input                         true
% 23.98/3.50  --eq_ax_congr_red                       true
% 23.98/3.50  --pure_diseq_elim                       true
% 23.98/3.50  --brand_transform                       false
% 23.98/3.50  --non_eq_to_eq                          false
% 23.98/3.50  --prep_def_merge                        true
% 23.98/3.50  --prep_def_merge_prop_impl              false
% 23.98/3.50  --prep_def_merge_mbd                    true
% 23.98/3.50  --prep_def_merge_tr_red                 false
% 23.98/3.50  --prep_def_merge_tr_cl                  false
% 23.98/3.50  --smt_preprocessing                     true
% 23.98/3.50  --smt_ac_axioms                         fast
% 23.98/3.50  --preprocessed_out                      false
% 23.98/3.50  --preprocessed_stats                    false
% 23.98/3.50  
% 23.98/3.50  ------ Abstraction refinement Options
% 23.98/3.50  
% 23.98/3.50  --abstr_ref                             []
% 23.98/3.50  --abstr_ref_prep                        false
% 23.98/3.50  --abstr_ref_until_sat                   false
% 23.98/3.50  --abstr_ref_sig_restrict                funpre
% 23.98/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.98/3.50  --abstr_ref_under                       []
% 23.98/3.50  
% 23.98/3.50  ------ SAT Options
% 23.98/3.50  
% 23.98/3.50  --sat_mode                              false
% 23.98/3.50  --sat_fm_restart_options                ""
% 23.98/3.50  --sat_gr_def                            false
% 23.98/3.50  --sat_epr_types                         true
% 23.98/3.50  --sat_non_cyclic_types                  false
% 23.98/3.50  --sat_finite_models                     false
% 23.98/3.50  --sat_fm_lemmas                         false
% 23.98/3.50  --sat_fm_prep                           false
% 23.98/3.50  --sat_fm_uc_incr                        true
% 23.98/3.50  --sat_out_model                         small
% 23.98/3.50  --sat_out_clauses                       false
% 23.98/3.50  
% 23.98/3.50  ------ QBF Options
% 23.98/3.50  
% 23.98/3.50  --qbf_mode                              false
% 23.98/3.50  --qbf_elim_univ                         false
% 23.98/3.50  --qbf_dom_inst                          none
% 23.98/3.50  --qbf_dom_pre_inst                      false
% 23.98/3.50  --qbf_sk_in                             false
% 23.98/3.50  --qbf_pred_elim                         true
% 23.98/3.50  --qbf_split                             512
% 23.98/3.50  
% 23.98/3.50  ------ BMC1 Options
% 23.98/3.50  
% 23.98/3.50  --bmc1_incremental                      false
% 23.98/3.50  --bmc1_axioms                           reachable_all
% 23.98/3.50  --bmc1_min_bound                        0
% 23.98/3.50  --bmc1_max_bound                        -1
% 23.98/3.50  --bmc1_max_bound_default                -1
% 23.98/3.50  --bmc1_symbol_reachability              true
% 23.98/3.50  --bmc1_property_lemmas                  false
% 23.98/3.50  --bmc1_k_induction                      false
% 23.98/3.50  --bmc1_non_equiv_states                 false
% 23.98/3.50  --bmc1_deadlock                         false
% 23.98/3.50  --bmc1_ucm                              false
% 23.98/3.50  --bmc1_add_unsat_core                   none
% 23.98/3.50  --bmc1_unsat_core_children              false
% 23.98/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.98/3.50  --bmc1_out_stat                         full
% 23.98/3.50  --bmc1_ground_init                      false
% 23.98/3.50  --bmc1_pre_inst_next_state              false
% 23.98/3.50  --bmc1_pre_inst_state                   false
% 23.98/3.50  --bmc1_pre_inst_reach_state             false
% 23.98/3.50  --bmc1_out_unsat_core                   false
% 23.98/3.50  --bmc1_aig_witness_out                  false
% 23.98/3.50  --bmc1_verbose                          false
% 23.98/3.50  --bmc1_dump_clauses_tptp                false
% 23.98/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.98/3.50  --bmc1_dump_file                        -
% 23.98/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.98/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.98/3.50  --bmc1_ucm_extend_mode                  1
% 23.98/3.50  --bmc1_ucm_init_mode                    2
% 23.98/3.50  --bmc1_ucm_cone_mode                    none
% 23.98/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.98/3.50  --bmc1_ucm_relax_model                  4
% 23.98/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.98/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.98/3.50  --bmc1_ucm_layered_model                none
% 23.98/3.50  --bmc1_ucm_max_lemma_size               10
% 23.98/3.50  
% 23.98/3.50  ------ AIG Options
% 23.98/3.50  
% 23.98/3.50  --aig_mode                              false
% 23.98/3.50  
% 23.98/3.50  ------ Instantiation Options
% 23.98/3.50  
% 23.98/3.50  --instantiation_flag                    true
% 23.98/3.50  --inst_sos_flag                         false
% 23.98/3.50  --inst_sos_phase                        true
% 23.98/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.98/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.98/3.50  --inst_lit_sel_side                     none
% 23.98/3.50  --inst_solver_per_active                1400
% 23.98/3.50  --inst_solver_calls_frac                1.
% 23.98/3.50  --inst_passive_queue_type               priority_queues
% 23.98/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.98/3.50  --inst_passive_queues_freq              [25;2]
% 23.98/3.50  --inst_dismatching                      true
% 23.98/3.50  --inst_eager_unprocessed_to_passive     true
% 23.98/3.50  --inst_prop_sim_given                   true
% 23.98/3.50  --inst_prop_sim_new                     false
% 23.98/3.50  --inst_subs_new                         false
% 23.98/3.50  --inst_eq_res_simp                      false
% 23.98/3.50  --inst_subs_given                       false
% 23.98/3.50  --inst_orphan_elimination               true
% 23.98/3.50  --inst_learning_loop_flag               true
% 23.98/3.50  --inst_learning_start                   3000
% 23.98/3.50  --inst_learning_factor                  2
% 23.98/3.50  --inst_start_prop_sim_after_learn       3
% 23.98/3.50  --inst_sel_renew                        solver
% 23.98/3.50  --inst_lit_activity_flag                true
% 23.98/3.50  --inst_restr_to_given                   false
% 23.98/3.50  --inst_activity_threshold               500
% 23.98/3.50  --inst_out_proof                        true
% 23.98/3.50  
% 23.98/3.50  ------ Resolution Options
% 23.98/3.50  
% 23.98/3.50  --resolution_flag                       false
% 23.98/3.50  --res_lit_sel                           adaptive
% 23.98/3.50  --res_lit_sel_side                      none
% 23.98/3.50  --res_ordering                          kbo
% 23.98/3.50  --res_to_prop_solver                    active
% 23.98/3.50  --res_prop_simpl_new                    false
% 23.98/3.50  --res_prop_simpl_given                  true
% 23.98/3.50  --res_passive_queue_type                priority_queues
% 23.98/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.98/3.50  --res_passive_queues_freq               [15;5]
% 23.98/3.50  --res_forward_subs                      full
% 23.98/3.50  --res_backward_subs                     full
% 23.98/3.50  --res_forward_subs_resolution           true
% 23.98/3.50  --res_backward_subs_resolution          true
% 23.98/3.50  --res_orphan_elimination                true
% 23.98/3.50  --res_time_limit                        2.
% 23.98/3.50  --res_out_proof                         true
% 23.98/3.50  
% 23.98/3.50  ------ Superposition Options
% 23.98/3.50  
% 23.98/3.50  --superposition_flag                    true
% 23.98/3.50  --sup_passive_queue_type                priority_queues
% 23.98/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.98/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.98/3.50  --demod_completeness_check              fast
% 23.98/3.50  --demod_use_ground                      true
% 23.98/3.50  --sup_to_prop_solver                    passive
% 23.98/3.50  --sup_prop_simpl_new                    true
% 23.98/3.50  --sup_prop_simpl_given                  true
% 23.98/3.50  --sup_fun_splitting                     false
% 23.98/3.50  --sup_smt_interval                      50000
% 23.98/3.50  
% 23.98/3.50  ------ Superposition Simplification Setup
% 23.98/3.50  
% 23.98/3.50  --sup_indices_passive                   []
% 23.98/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.98/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.98/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_full_bw                           [BwDemod]
% 23.98/3.50  --sup_immed_triv                        [TrivRules]
% 23.98/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.98/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_immed_bw_main                     []
% 23.98/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.98/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.98/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.98/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.98/3.50  
% 23.98/3.50  ------ Combination Options
% 23.98/3.50  
% 23.98/3.50  --comb_res_mult                         3
% 23.98/3.50  --comb_sup_mult                         2
% 23.98/3.50  --comb_inst_mult                        10
% 23.98/3.50  
% 23.98/3.50  ------ Debug Options
% 23.98/3.50  
% 23.98/3.50  --dbg_backtrace                         false
% 23.98/3.50  --dbg_dump_prop_clauses                 false
% 23.98/3.50  --dbg_dump_prop_clauses_file            -
% 23.98/3.50  --dbg_out_stat                          false
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  ------ Proving...
% 23.98/3.50  
% 23.98/3.50  
% 23.98/3.50  % SZS status Theorem for theBenchmark.p
% 23.98/3.50  
% 23.98/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.98/3.50  
% 23.98/3.50  fof(f1,axiom,(
% 23.98/3.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.98/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.98/3.50  
% 23.98/3.50  fof(f15,plain,(
% 23.98/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.98/3.50    inference(nnf_transformation,[],[f1])).
% 23.98/3.50  
% 23.98/3.50  fof(f16,plain,(
% 23.98/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.98/3.50    inference(flattening,[],[f15])).
% 23.98/3.50  
% 23.98/3.50  fof(f17,plain,(
% 23.98/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.98/3.50    inference(rectify,[],[f16])).
% 23.98/3.50  
% 23.98/3.50  fof(f18,plain,(
% 23.98/3.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f19,plain,(
% 23.98/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.98/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 23.98/3.50  
% 23.98/3.50  fof(f38,plain,(
% 23.98/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.98/3.50    inference(cnf_transformation,[],[f19])).
% 23.98/3.50  
% 23.98/3.50  fof(f67,plain,(
% 23.98/3.50    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 23.98/3.50    inference(equality_resolution,[],[f38])).
% 23.98/3.50  
% 23.98/3.50  fof(f68,plain,(
% 23.98/3.50    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 23.98/3.50    inference(equality_resolution,[],[f67])).
% 23.98/3.50  
% 23.98/3.50  fof(f4,conjecture,(
% 23.98/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 23.98/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.98/3.50  
% 23.98/3.50  fof(f5,negated_conjecture,(
% 23.98/3.50    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 23.98/3.50    inference(negated_conjecture,[],[f4])).
% 23.98/3.50  
% 23.98/3.50  fof(f10,plain,(
% 23.98/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | (~r1_lattice3(X0,k2_tarski(X2,X3),X1) & (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 23.98/3.50    inference(ennf_transformation,[],[f5])).
% 23.98/3.50  
% 23.98/3.50  fof(f11,plain,(
% 23.98/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | (~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 23.98/3.50    inference(flattening,[],[f10])).
% 23.98/3.50  
% 23.98/3.50  fof(f13,plain,(
% 23.98/3.50    ! [X1,X3,X2,X0] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~sP1(X1,X3,X2,X0))),
% 23.98/3.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 23.98/3.50  
% 23.98/3.50  fof(f12,plain,(
% 23.98/3.50    ! [X1,X3,X2,X0] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~sP0(X1,X3,X2,X0))),
% 23.98/3.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 23.98/3.50  
% 23.98/3.50  fof(f14,plain,(
% 23.98/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 23.98/3.50    inference(definition_folding,[],[f11,f13,f12])).
% 23.98/3.50  
% 23.98/3.50  fof(f35,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) => ((sP1(X1,sK8,X2,X0) | ((~r1_orders_2(X0,sK8,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,sK8),X1)) | sP0(X1,sK8,X2,X0) | ((~r1_orders_2(X0,X1,sK8) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,sK8),X1))) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f34,plain,(
% 23.98/3.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : ((sP1(X1,X3,sK7,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,sK7,X1)) & r2_lattice3(X0,k2_tarski(sK7,X3),X1)) | sP0(X1,X3,sK7,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,sK7)) & r1_lattice3(X0,k2_tarski(sK7,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f33,plain,(
% 23.98/3.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : ((sP1(sK6,X3,X2,X0) | ((~r1_orders_2(X0,X3,sK6) | ~r1_orders_2(X0,X2,sK6)) & r2_lattice3(X0,k2_tarski(X2,X3),sK6)) | sP0(sK6,X3,X2,X0) | ((~r1_orders_2(X0,sK6,X3) | ~r1_orders_2(X0,sK6,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),sK6))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f32,plain,(
% 23.98/3.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,sK5) | ((~r1_orders_2(sK5,X3,X1) | ~r1_orders_2(sK5,X2,X1)) & r2_lattice3(sK5,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,sK5) | ((~r1_orders_2(sK5,X1,X3) | ~r1_orders_2(sK5,X1,X2)) & r1_lattice3(sK5,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_orders_2(sK5))),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f36,plain,(
% 23.98/3.50    ((((sP1(sK6,sK8,sK7,sK5) | ((~r1_orders_2(sK5,sK8,sK6) | ~r1_orders_2(sK5,sK7,sK6)) & r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)) | sP0(sK6,sK8,sK7,sK5) | ((~r1_orders_2(sK5,sK6,sK8) | ~r1_orders_2(sK5,sK6,sK7)) & r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6))) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_orders_2(sK5)),
% 23.98/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f14,f35,f34,f33,f32])).
% 23.98/3.50  
% 23.98/3.50  fof(f58,plain,(
% 23.98/3.50    m1_subset_1(sK6,u1_struct_0(sK5))),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f2,axiom,(
% 23.98/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 23.98/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.98/3.50  
% 23.98/3.50  fof(f6,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(ennf_transformation,[],[f2])).
% 23.98/3.50  
% 23.98/3.50  fof(f7,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(flattening,[],[f6])).
% 23.98/3.50  
% 23.98/3.50  fof(f20,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(nnf_transformation,[],[f7])).
% 23.98/3.50  
% 23.98/3.50  fof(f21,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(rectify,[],[f20])).
% 23.98/3.50  
% 23.98/3.50  fof(f22,plain,(
% 23.98/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f23,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 23.98/3.50  
% 23.98/3.50  fof(f44,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f23])).
% 23.98/3.50  
% 23.98/3.50  fof(f57,plain,(
% 23.98/3.50    l1_orders_2(sK5)),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f39,plain,(
% 23.98/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.98/3.50    inference(cnf_transformation,[],[f19])).
% 23.98/3.50  
% 23.98/3.50  fof(f65,plain,(
% 23.98/3.50    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 23.98/3.50    inference(equality_resolution,[],[f39])).
% 23.98/3.50  
% 23.98/3.50  fof(f66,plain,(
% 23.98/3.50    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 23.98/3.50    inference(equality_resolution,[],[f65])).
% 23.98/3.50  
% 23.98/3.50  fof(f3,axiom,(
% 23.98/3.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 23.98/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.98/3.50  
% 23.98/3.50  fof(f8,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(ennf_transformation,[],[f3])).
% 23.98/3.50  
% 23.98/3.50  fof(f9,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(flattening,[],[f8])).
% 23.98/3.50  
% 23.98/3.50  fof(f24,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(nnf_transformation,[],[f9])).
% 23.98/3.50  
% 23.98/3.50  fof(f25,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(rectify,[],[f24])).
% 23.98/3.50  
% 23.98/3.50  fof(f26,plain,(
% 23.98/3.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 23.98/3.50    introduced(choice_axiom,[])).
% 23.98/3.50  
% 23.98/3.50  fof(f27,plain,(
% 23.98/3.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 23.98/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 23.98/3.50  
% 23.98/3.50  fof(f49,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f27])).
% 23.98/3.50  
% 23.98/3.50  fof(f37,plain,(
% 23.98/3.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 23.98/3.50    inference(cnf_transformation,[],[f19])).
% 23.98/3.50  
% 23.98/3.50  fof(f69,plain,(
% 23.98/3.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 23.98/3.50    inference(equality_resolution,[],[f37])).
% 23.98/3.50  
% 23.98/3.50  fof(f47,plain,(
% 23.98/3.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f27])).
% 23.98/3.50  
% 23.98/3.50  fof(f46,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f23])).
% 23.98/3.50  
% 23.98/3.50  fof(f30,plain,(
% 23.98/3.50    ! [X1,X3,X2,X0] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~sP0(X1,X3,X2,X0))),
% 23.98/3.50    inference(nnf_transformation,[],[f12])).
% 23.98/3.50  
% 23.98/3.50  fof(f31,plain,(
% 23.98/3.50    ! [X0,X1,X2,X3] : ((~r1_lattice3(X3,k2_tarski(X2,X1),X0) & r1_orders_2(X3,X0,X1) & r1_orders_2(X3,X0,X2)) | ~sP0(X0,X1,X2,X3))),
% 23.98/3.50    inference(rectify,[],[f30])).
% 23.98/3.50  
% 23.98/3.50  fof(f56,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (~r1_lattice3(X3,k2_tarski(X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f31])).
% 23.98/3.50  
% 23.98/3.50  fof(f28,plain,(
% 23.98/3.50    ! [X1,X3,X2,X0] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~sP1(X1,X3,X2,X0))),
% 23.98/3.50    inference(nnf_transformation,[],[f13])).
% 23.98/3.50  
% 23.98/3.50  fof(f29,plain,(
% 23.98/3.50    ! [X0,X1,X2,X3] : ((~r2_lattice3(X3,k2_tarski(X2,X1),X0) & r1_orders_2(X3,X1,X0) & r1_orders_2(X3,X2,X0)) | ~sP1(X0,X1,X2,X3))),
% 23.98/3.50    inference(rectify,[],[f28])).
% 23.98/3.50  
% 23.98/3.50  fof(f53,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (~r2_lattice3(X3,k2_tarski(X2,X1),X0) | ~sP1(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f29])).
% 23.98/3.50  
% 23.98/3.50  fof(f64,plain,(
% 23.98/3.50    sP1(sK6,sK8,sK7,sK5) | ~r1_orders_2(sK5,sK8,sK6) | ~r1_orders_2(sK5,sK7,sK6) | sP0(sK6,sK8,sK7,sK5) | ~r1_orders_2(sK5,sK6,sK8) | ~r1_orders_2(sK5,sK6,sK7)),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f60,plain,(
% 23.98/3.50    m1_subset_1(sK8,u1_struct_0(sK5))),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f43,plain,(
% 23.98/3.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f23])).
% 23.98/3.50  
% 23.98/3.50  fof(f59,plain,(
% 23.98/3.50    m1_subset_1(sK7,u1_struct_0(sK5))),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f45,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f23])).
% 23.98/3.50  
% 23.98/3.50  fof(f52,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X3,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f29])).
% 23.98/3.50  
% 23.98/3.50  fof(f62,plain,(
% 23.98/3.50    sP1(sK6,sK8,sK7,sK5) | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) | sP0(sK6,sK8,sK7,sK5) | ~r1_orders_2(sK5,sK6,sK8) | ~r1_orders_2(sK5,sK6,sK7)),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f55,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X3,X0,X1) | ~sP0(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f31])).
% 23.98/3.50  
% 23.98/3.50  fof(f61,plain,(
% 23.98/3.50    sP1(sK6,sK8,sK7,sK5) | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) | sP0(sK6,sK8,sK7,sK5) | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f54,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X3,X0,X2) | ~sP0(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f31])).
% 23.98/3.50  
% 23.98/3.50  fof(f51,plain,(
% 23.98/3.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X3,X2,X0) | ~sP1(X0,X1,X2,X3)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f29])).
% 23.98/3.50  
% 23.98/3.50  fof(f63,plain,(
% 23.98/3.50    sP1(sK6,sK8,sK7,sK5) | ~r1_orders_2(sK5,sK8,sK6) | ~r1_orders_2(sK5,sK7,sK6) | sP0(sK6,sK8,sK7,sK5) | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)),
% 23.98/3.50    inference(cnf_transformation,[],[f36])).
% 23.98/3.50  
% 23.98/3.50  fof(f50,plain,(
% 23.98/3.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 23.98/3.50    inference(cnf_transformation,[],[f27])).
% 23.98/3.50  
% 23.98/3.50  cnf(c_4,plain,
% 23.98/3.50      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 23.98/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_6266,plain,
% 23.98/3.50      ( r2_hidden(sK7,k2_tarski(sK7,X0)) ),
% 23.98/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_78010,plain,
% 23.98/3.50      ( r2_hidden(sK7,k2_tarski(sK7,sK8)) ),
% 23.98/3.50      inference(instantiation,[status(thm)],[c_6266]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_26,negated_conjecture,
% 23.98/3.50      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5619,plain,
% 23.98/3.50      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_8,plain,
% 23.98/3.50      ( r1_lattice3(X0,X1,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 23.98/3.50      | ~ l1_orders_2(X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_27,negated_conjecture,
% 23.98/3.50      ( l1_orders_2(sK5) ),
% 23.98/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_390,plain,
% 23.98/3.50      ( r1_lattice3(X0,X1,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 23.98/3.50      | sK5 != X0 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_391,plain,
% 23.98/3.50      ( r1_lattice3(sK5,X0,X1)
% 23.98/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.50      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) ),
% 23.98/3.50      inference(unflattening,[status(thm)],[c_390]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5613,plain,
% 23.98/3.50      ( r1_lattice3(sK5,X0,X1) = iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | m1_subset_1(sK3(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_3,plain,
% 23.98/3.50      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 23.98/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5624,plain,
% 23.98/3.50      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_11,plain,
% 23.98/3.50      ( r2_lattice3(X0,X1,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | r2_hidden(sK4(X0,X1,X2),X1)
% 23.98/3.50      | ~ l1_orders_2(X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_339,plain,
% 23.98/3.50      ( r2_lattice3(X0,X1,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | r2_hidden(sK4(X0,X1,X2),X1)
% 23.98/3.50      | sK5 != X0 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_340,plain,
% 23.98/3.50      ( r2_lattice3(sK5,X0,X1)
% 23.98/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.50      | r2_hidden(sK4(sK5,X0,X1),X0) ),
% 23.98/3.50      inference(unflattening,[status(thm)],[c_339]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5616,plain,
% 23.98/3.50      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | r2_hidden(sK4(sK5,X0,X1),X0) = iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5,plain,
% 23.98/3.50      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 23.98/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5622,plain,
% 23.98/3.50      ( X0 = X1
% 23.98/3.50      | X0 = X2
% 23.98/3.50      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_7578,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,X1),X2) = X1
% 23.98/3.50      | r2_lattice3(sK5,k2_tarski(X0,X1),X2) = iProver_top
% 23.98/3.50      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_5616,c_5622]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_13,plain,
% 23.98/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 23.98/3.50      | r1_orders_2(X0,X3,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.98/3.50      | ~ r2_hidden(X3,X1)
% 23.98/3.50      | ~ l1_orders_2(X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_303,plain,
% 23.98/3.50      ( ~ r2_lattice3(X0,X1,X2)
% 23.98/3.50      | r1_orders_2(X0,X3,X2)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 23.98/3.50      | ~ r2_hidden(X3,X1)
% 23.98/3.50      | sK5 != X0 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_304,plain,
% 23.98/3.50      ( ~ r2_lattice3(sK5,X0,X1)
% 23.98/3.50      | r1_orders_2(sK5,X2,X1)
% 23.98/3.50      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 23.98/3.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.50      | ~ r2_hidden(X2,X0) ),
% 23.98/3.50      inference(unflattening,[status(thm)],[c_303]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5618,plain,
% 23.98/3.50      ( r2_lattice3(sK5,X0,X1) != iProver_top
% 23.98/3.50      | r1_orders_2(sK5,X2,X1) = iProver_top
% 23.98/3.50      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | r2_hidden(X2,X0) != iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_8646,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,X1),X2) = X1
% 23.98/3.50      | r1_orders_2(sK5,X3,X2) = iProver_top
% 23.98/3.50      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_7578,c_5618]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_11945,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,X1),X2) = X1
% 23.98/3.50      | r1_orders_2(sK5,X1,X2) = iProver_top
% 23.98/3.50      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_5624,c_8646]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_14417,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X1
% 23.98/3.50      | r1_orders_2(sK5,X1,sK3(sK5,X2,X3)) = iProver_top
% 23.98/3.50      | r1_lattice3(sK5,X2,X3) = iProver_top
% 23.98/3.50      | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_5613,c_11945]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_6,plain,
% 23.98/3.50      ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X1))
% 23.98/3.50      | r1_lattice3(X0,X2,X1)
% 23.98/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.98/3.50      | ~ l1_orders_2(X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_420,plain,
% 23.98/3.50      ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X1))
% 23.98/3.50      | r1_lattice3(X0,X2,X1)
% 23.98/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.98/3.50      | sK5 != X0 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_421,plain,
% 23.98/3.50      ( ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
% 23.98/3.50      | r1_lattice3(sK5,X1,X0)
% 23.98/3.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 23.98/3.50      inference(unflattening,[status(thm)],[c_420]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_5611,plain,
% 23.98/3.50      ( r1_orders_2(sK5,X0,sK3(sK5,X1,X0)) != iProver_top
% 23.98/3.50      | r1_lattice3(sK5,X1,X0) = iProver_top
% 23.98/3.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.50      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_20118,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X1)) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X1)) = X1
% 23.98/3.50      | r1_lattice3(sK5,X2,X1) = iProver_top
% 23.98/3.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_14417,c_5611]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_20351,plain,
% 23.98/3.50      ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,X1,sK6)) = X0
% 23.98/3.50      | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,X1,sK6)) = sK6
% 23.98/3.50      | r1_lattice3(sK5,X1,sK6) = iProver_top ),
% 23.98/3.50      inference(superposition,[status(thm)],[c_5619,c_20118]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_17,plain,
% 23.98/3.50      ( ~ sP0(X0,X1,X2,X3) | ~ r1_lattice3(X3,k2_tarski(X2,X1),X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_14,plain,
% 23.98/3.50      ( ~ sP1(X0,X1,X2,X3) | ~ r2_lattice3(X3,k2_tarski(X2,X1),X0) ),
% 23.98/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_20,negated_conjecture,
% 23.98/3.50      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.50      | sP1(sK6,sK8,sK7,sK5)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_1097,plain,
% 23.98/3.50      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.50      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.50      | sK5 != X0
% 23.98/3.50      | sK7 != X1
% 23.98/3.50      | sK8 != X2
% 23.98/3.50      | sK6 != X3 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_1098,plain,
% 23.98/3.50      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.50      | ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.50      inference(unflattening,[status(thm)],[c_1097]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_1582,plain,
% 23.98/3.50      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.50      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
% 23.98/3.50      | sK5 != X0
% 23.98/3.50      | sK7 != X1
% 23.98/3.50      | sK8 != X2
% 23.98/3.50      | sK6 != X3 ),
% 23.98/3.50      inference(resolution_lifted,[status(thm)],[c_17,c_1098]) ).
% 23.98/3.50  
% 23.98/3.50  cnf(c_1583,plain,
% 23.98/3.50      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.50      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1582]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5604,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8645,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7578,c_5604]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_29,plain,
% 23.98/3.51      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_24,negated_conjecture,
% 23.98/3.51      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(cnf_transformation,[],[f60]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_31,plain,
% 23.98/3.51      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9,plain,
% 23.98/3.51      ( r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_lattice3(X0,X3,X1)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | ~ r2_hidden(X2,X3)
% 23.98/3.51      | ~ l1_orders_2(X0) ),
% 23.98/3.51      inference(cnf_transformation,[],[f43]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_369,plain,
% 23.98/3.51      ( r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_lattice3(X0,X3,X1)
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.98/3.51      | ~ r2_hidden(X2,X3)
% 23.98/3.51      | sK5 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_370,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1)
% 23.98/3.51      | ~ r1_lattice3(sK5,X2,X0)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X1,X2) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_369]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5970,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,X1,X0)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK8,X1) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_370]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6542,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(X1,sK8),X0)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK8,k2_tarski(X1,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5970]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6989,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(X0,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK8,k2_tarski(X0,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6542]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8864,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK8,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6989]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8865,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK8,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_8864]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6228,plain,
% 23.98/3.51      ( r2_hidden(sK8,k2_tarski(X0,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_3]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_10304,plain,
% 23.98/3.51      ( r2_hidden(sK8,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6228]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_10305,plain,
% 23.98/3.51      ( r2_hidden(sK8,k2_tarski(sK7,sK8)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_10304]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13248,plain,
% 23.98/3.51      ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_8645,c_29,c_31,c_8865,c_10305]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13249,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_13248]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_21076,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_20351,c_13249]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_25,negated_conjecture,
% 23.98/3.51      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(cnf_transformation,[],[f59]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_30,plain,
% 23.98/3.51      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_75,plain,
% 23.98/3.51      ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5)) | sK5 = sK5 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_78,plain,
% 23.98/3.51      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_4]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_7,plain,
% 23.98/3.51      ( r1_lattice3(X0,X1,X2)
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | r2_hidden(sK3(X0,X1,X2),X1)
% 23.98/3.51      | ~ l1_orders_2(X0) ),
% 23.98/3.51      inference(cnf_transformation,[],[f45]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_405,plain,
% 23.98/3.51      ( r1_lattice3(X0,X1,X2)
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | r2_hidden(sK3(X0,X1,X2),X1)
% 23.98/3.51      | sK5 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_406,plain,
% 23.98/3.51      ( r1_lattice3(sK5,X0,X1)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | r2_hidden(sK3(sK5,X0,X1),X0) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_405]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2520,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | r2_hidden(sK3(sK5,X1,X0),X1)
% 23.98/3.51      | k2_tarski(sK7,sK8) != X1
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1583,c_406]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2521,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2520]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2522,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2521]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2618,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | k2_tarski(sK7,sK8) != X1
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1583,c_421]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2619,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2620,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5151,plain,( X0 = X0 ),theory(equality) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6220,plain,
% 23.98/3.51      ( sK6 = sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5151]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5157,plain,
% 23.98/3.51      ( ~ r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_orders_2(X3,X4,X5)
% 23.98/3.51      | X3 != X0
% 23.98/3.51      | X4 != X1
% 23.98/3.51      | X5 != X2 ),
% 23.98/3.51      theory(equality) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_11130,plain,
% 23.98/3.51      ( r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | X0 != sK5
% 23.98/3.51      | X2 != sK8
% 23.98/3.51      | X1 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5157]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23332,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK8
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_11130]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23348,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK8
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_23332]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_11135,plain,
% 23.98/3.51      ( r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | X0 != sK5
% 23.98/3.51      | X2 != sK7
% 23.98/3.51      | X1 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5157]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23331,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK7
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_11135]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23350,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) != sK7
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_23331]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_15,plain,
% 23.98/3.51      ( ~ sP1(X0,X1,X2,X3) | r1_orders_2(X3,X1,X0) ),
% 23.98/3.51      inference(cnf_transformation,[],[f52]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_22,negated_conjecture,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | sP1(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.51      inference(cnf_transformation,[],[f62]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1051,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X3
% 23.98/3.51      | sK8 != X1
% 23.98/3.51      | sK6 != X2 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1052,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1051]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1606,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X1
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X3 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_17,c_1052]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1607,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1606]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5603,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1607]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_21077,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_20351,c_5603]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2595,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | k2_tarski(sK7,sK8) != X1
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1607,c_421]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2596,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2595]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2597,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2596]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_18,plain,
% 23.98/3.51      ( ~ sP0(X0,X1,X2,X3) | r1_orders_2(X3,X0,X1) ),
% 23.98/3.51      inference(cnf_transformation,[],[f55]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23,negated_conjecture,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | sP1(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(cnf_transformation,[],[f61]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1035,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X3
% 23.98/3.51      | sK8 != X1
% 23.98/3.51      | sK6 != X2 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1036,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1035]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1548,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X3
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_18,c_1036]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1549,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1548]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5606,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8341,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5606,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2970,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,X2)
% 23.98/3.51      | k2_tarski(sK7,sK8) != X2
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1549,c_304]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2971,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2970]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2972,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2971]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12299,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_8341,c_29,c_31,c_2972,c_8865,c_10305]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12300,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12299]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12311,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5624,c_12300]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12481,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12311,c_31]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12482,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12481]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_19,plain,
% 23.98/3.51      ( ~ sP0(X0,X1,X2,X3) | r1_orders_2(X3,X0,X2) ),
% 23.98/3.51      inference(cnf_transformation,[],[f54]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1491,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X2
% 23.98/3.51      | sK8 != X3
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_19,c_1036]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1492,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1491]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5609,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9397,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5609,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3030,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,X2)
% 23.98/3.51      | k2_tarski(sK7,sK8) != X2
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1492,c_304]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3031,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_3030]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3035,plain,
% 23.98/3.51      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_3031,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3036,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_3035]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3037,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_3036]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12605,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_9397,c_3037]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12606,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12605]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12618,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5616,c_12606]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12616,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5624,c_12606]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13124,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12618,c_31,c_12616]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5620,plain,
% 23.98/3.51      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5614,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X2,X0) != iProver_top
% 23.98/3.51      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X1,X2) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6017,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X1,X0) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK7,X1) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5620,c_5614]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6493,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X0,sK6) != iProver_top
% 23.98/3.51      | r2_hidden(sK7,X0) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5619,c_6017]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13134,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_13124,c_6493]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5623,plain,
% 23.98/3.51      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13245,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
% 23.98/3.51      inference(forward_subsumption_resolution,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_13134,c_5623]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5612,plain,
% 23.98/3.51      ( r1_lattice3(sK5,X0,X1) = iProver_top
% 23.98/3.51      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK3(sK5,X0,X1),X0) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_7389,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(X0,X1),X2) = X0
% 23.98/3.51      | sK3(sK5,k2_tarski(X0,X1),X2) = X1
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(X0,X1),X2) = iProver_top
% 23.98/3.51      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5612,c_5622]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8482,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7389,c_5603]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12392,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_8482,c_29,c_31,c_12311]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12404,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_12392,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12967,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12404,c_29]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12968,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12967]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12983,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5616,c_12968]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12981,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5624,c_12968]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13662,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7 ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12983,c_31,c_12981,c_13245]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13663,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_13662]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27101,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_21077,c_29,c_75,c_78,c_2597,c_6220,c_12482,c_13245,
% 23.98/3.51                 c_13663,c_23348,c_23350]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27110,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_27101,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27425,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_27110,c_29]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27426,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_27425]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27436,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5624,c_27426]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_16,plain,
% 23.98/3.51      ( ~ sP1(X0,X1,X2,X3) | r1_orders_2(X3,X2,X0) ),
% 23.98/3.51      inference(cnf_transformation,[],[f51]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1012,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X1
% 23.98/3.51      | sK8 != X3
% 23.98/3.51      | sK6 != X2 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1013,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1012]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1627,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X1
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X3 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_17,c_1013]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1628,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1627]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5602,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1628]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_21078,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,sK6),sK3(sK5,k2_tarski(sK7,sK8),sK6)) = sK6
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_20351,c_5602]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2572,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,X0,sK3(sK5,X1,X0))
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | k2_tarski(sK7,sK8) != X1
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1628,c_421]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2573,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2572]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2575,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_2573,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2576,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK6,sK8) ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_2575]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2577,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_996,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X1
% 23.98/3.51      | sK8 != X3
% 23.98/3.51      | sK6 != X2 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_997,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_996]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1566,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X3
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_18,c_997]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1567,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1566]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5605,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8319,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5605,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2940,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,X2)
% 23.98/3.51      | k2_tarski(sK7,sK8) != X2
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1567,c_304]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2941,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_2940]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2945,plain,
% 23.98/3.51      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_2941,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2946,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_2945]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_2947,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_2946]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12219,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_8319,c_29,c_31,c_2947,c_8865,c_10305]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12220,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12219]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12232,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5623,c_12220]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12425,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12232,c_30]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12426,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12425]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1509,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X2
% 23.98/3.51      | sK8 != X3
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_19,c_997]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1510,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1509]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5608,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9375,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5608,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3000,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,X1)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,X2)
% 23.98/3.51      | k2_tarski(sK7,sK8) != X2
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1510,c_304]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3001,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_3000]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3005,plain,
% 23.98/3.51      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_3001,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3006,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(X0,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_3005]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3007,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_3006]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12506,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_9375,c_29,c_3002]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12507,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_12506]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12519,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),X0) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),X0),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK4(sK5,k2_tarski(sK7,sK8),X0),u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5616,c_12507]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12518,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5623,c_12507]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13069,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12519,c_30,c_12518]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13079,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_13069,c_6493]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13116,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top ),
% 23.98/3.51      inference(forward_subsumption_resolution,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_13079,c_5623]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8483,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7389,c_5602]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12810,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_8483,c_29,c_30,c_12232]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12822,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_12810,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13386,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_12822,c_29,c_13116]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13387,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_13386]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13400,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5623,c_13387]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28013,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_21078,c_30,c_75,c_78,c_2577,c_6220,c_12426,c_13116,
% 23.98/3.51                 c_13400,c_23348,c_23350]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28022,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_28013,c_5618]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28172,plain,
% 23.98/3.51      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_28022,c_29]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28173,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(X0,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_28172]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28184,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5623,c_28173]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_21,negated_conjecture,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | sP1(sK6,sK8,sK7,sK5)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(cnf_transformation,[],[f63]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1078,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X1
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X3 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1079,plain,
% 23.98/3.51      ( sP0(sK6,sK8,sK7,sK5)
% 23.98/3.51      | ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1078]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1527,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X3
% 23.98/3.51      | sK8 != X2
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_18,c_1079]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1528,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1527]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5607,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9783,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7578,c_5607]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1470,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK5 != X0
% 23.98/3.51      | sK7 != X2
% 23.98/3.51      | sK8 != X3
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_19,c_1079]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_1471,plain,
% 23.98/3.51      ( ~ r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_1470]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5610,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9809,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7578,c_5610]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_13258,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_7389,c_13249]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5946,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK6,sK3(sK5,X0,sK6))
% 23.98/3.51      | r1_lattice3(sK5,X0,sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_421]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8868,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(X0,sK8),sK6))
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(X0,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5946]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_16721,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6))
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_8868]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_16722,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK3(sK5,k2_tarski(sK7,sK8),sK6)) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_16721]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35052,plain,
% 23.98/3.51      ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_9783,c_29,c_30,c_31,c_75,c_78,c_6220,c_9809,c_13258,
% 23.98/3.51                 c_16722,c_23348,c_23350,c_27436,c_28184]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35053,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_35052]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35061,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_35053,c_6493]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5975,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK7)
% 23.98/3.51      | ~ r1_lattice3(sK5,X1,X0)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK7,X1) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_370]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6563,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK7)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,X1),X0)
% 23.98/3.51      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK7,k2_tarski(sK7,X1)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5975]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_7034,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,X0),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK7,k2_tarski(sK7,X0)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6563]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9341,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | ~ r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 23.98/3.51      | ~ r2_hidden(sK7,k2_tarski(sK7,sK8)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_7034]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_9342,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) != iProver_top
% 23.98/3.51      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_9341]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35059,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_35053,c_13249]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35308,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_35061,c_30,c_31,c_27436,c_28184,c_35059]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35309,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_hidden(sK7,k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_35308]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35315,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
% 23.98/3.51      inference(forward_subsumption_resolution,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_35309,c_5623]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_10,plain,
% 23.98/3.51      ( r2_lattice3(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | ~ l1_orders_2(X0) ),
% 23.98/3.51      inference(cnf_transformation,[],[f50]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_354,plain,
% 23.98/3.51      ( r2_lattice3(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
% 23.98/3.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.98/3.51      | sK5 != X0 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_355,plain,
% 23.98/3.51      ( r2_lattice3(sK5,X0,X1)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_354]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5615,plain,
% 23.98/3.51      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,X0,X1),X1) != iProver_top
% 23.98/3.51      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35339,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_35315,c_5615]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35759,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_35339,c_29,c_30,c_28184]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6192,plain,
% 23.98/3.51      ( ~ r2_hidden(X0,k2_tarski(sK7,X1)) | X0 = X1 | X0 = sK7 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6665,plain,
% 23.98/3.51      ( ~ r2_hidden(X0,k2_tarski(sK7,sK8)) | X0 = sK7 | X0 = sK8 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6192]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_39598,plain,
% 23.98/3.51      ( ~ r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8))
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_6665]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_39607,plain,
% 23.98/3.51      ( sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK7
% 23.98/3.51      | sK3(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r2_hidden(sK3(sK5,k2_tarski(sK7,sK8),sK6),k2_tarski(sK7,sK8)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_39598]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_11946,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,X1),X2) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,X1),X2) = X1
% 23.98/3.51      | r1_orders_2(sK5,X0,X2) = iProver_top
% 23.98/3.51      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5623,c_8646]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_16139,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X3)) = X1
% 23.98/3.51      | r1_orders_2(sK5,X0,sK3(sK5,X2,X3)) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X2,X3) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5613,c_11946]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_23944,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X0)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(X0,X1),sK3(sK5,X2,X0)) = X1
% 23.98/3.51      | r1_lattice3(sK5,X2,X0) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_16139,c_5611]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_24066,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,X1,sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,X1,sK6)) = sK6
% 23.98/3.51      | r1_lattice3(sK5,X1,sK6) = iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5619,c_23944]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_7586,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK3(sK5,X1,X2)) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X3,X0) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X1,X2) = iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK3(sK5,X1,X2),X3) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5613,c_5614]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_10403,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK3(sK5,X1,X2)) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X1,X2) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(X3,sK3(sK5,X1,X2)),X0) != iProver_top
% 23.98/3.51      | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5624,c_7586]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_24409,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X2,X3) = iProver_top
% 23.98/3.51      | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_24066,c_10403]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_39991,plain,
% 23.98/3.51      ( m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X2,X3) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0 ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_24409,c_29]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_39992,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,X3)),sK6)) = sK6
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK3(sK5,X2,X3)) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X2,X3) = iProver_top
% 23.98/3.51      | m1_subset_1(X3,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_39991]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_40002,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
% 23.98/3.51      | r1_lattice3(sK5,X2,sK6) = iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_39992,c_5611]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_40007,plain,
% 23.98/3.51      ( r1_lattice3(sK5,X2,sK6) = iProver_top
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0 ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_40002,c_29]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_40008,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
% 23.98/3.51      | r1_lattice3(sK5,X2,sK6) = iProver_top ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_40007]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5621,plain,
% 23.98/3.51      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6016,plain,
% 23.98/3.51      ( r1_orders_2(sK5,X0,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X1,X0) != iProver_top
% 23.98/3.51      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 23.98/3.51      | r2_hidden(sK8,X1) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5621,c_5614]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_6082,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,X0,sK6) != iProver_top
% 23.98/3.51      | r2_hidden(sK8,X0) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_5619,c_6016]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_40018,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = X0
% 23.98/3.51      | sK4(sK5,k2_tarski(sK6,X0),sK3(sK5,k2_tarski(X1,sK3(sK5,X2,sK6)),sK6)) = sK6
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r2_hidden(sK8,X2) != iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_40008,c_6082]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3138,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | k2_tarski(sK7,sK8) != X0
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1528,c_355]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3139,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_3138]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3141,plain,
% 23.98/3.51      ( r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_3139,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3142,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) ),
% 23.98/3.51      inference(renaming,[status(thm)],[c_3141]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3143,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_3142]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35766,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK8) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_35759,c_5607]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_11081,plain,
% 23.98/3.51      ( r1_orders_2(X0,X1,X2)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | X0 != sK5
% 23.98/3.51      | X1 != sK8
% 23.98/3.51      | X2 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5157]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_37632,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) != sK8
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6 ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_11081]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_37639,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) != sK8
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != sK6
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_37632]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_40537,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK8) = iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_40018,c_29,c_30,c_31,c_75,c_78,c_3143,c_6220,c_8865,
% 23.98/3.51                 c_10305,c_27436,c_28184,c_35766,c_37639]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_41936,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_21076,c_29,c_30,c_31,c_75,c_78,c_2522,c_2620,c_3143,
% 23.98/3.51                 c_6220,c_8865,c_10305,c_23348,c_23350,c_27436,c_28184,
% 23.98/3.51                 c_35339,c_35766,c_37639,c_39607]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_5916,plain,
% 23.98/3.51      ( r2_lattice3(sK5,X0,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK4(sK5,X0,sK6),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_355]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_8274,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(X0,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(X0,sK8),sK6),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_5916]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12211,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(instantiation,[status(thm)],[c_8274]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_12212,plain,
% 23.98/3.51      ( r2_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6) != iProver_top
% 23.98/3.51      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 23.98/3.51      inference(predicate_to_equality,[status(thm)],[c_12211]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_41940,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK6,sK7) != iProver_top ),
% 23.98/3.51      inference(global_propositional_subsumption,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_41936,c_29,c_30,c_31,c_75,c_78,c_2522,c_2620,c_3143,
% 23.98/3.51                 c_6220,c_8865,c_10305,c_12212,c_23348,c_23350,c_27436,
% 23.98/3.51                 c_28184,c_35766,c_37639,c_39607]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_41942,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK6,sK7) ),
% 23.98/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_41940]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35765,plain,
% 23.98/3.51      ( sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8
% 23.98/3.51      | r1_orders_2(sK5,sK7,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK8,sK6) != iProver_top
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7) = iProver_top
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6) = iProver_top ),
% 23.98/3.51      inference(superposition,[status(thm)],[c_35759,c_5610]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_35811,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | sK4(sK5,k2_tarski(sK7,sK8),sK6) = sK8 ),
% 23.98/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_35765]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_28226,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK7,sK6) | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_28184]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_27485,plain,
% 23.98/3.51      ( r1_orders_2(sK5,sK8,sK6) | ~ m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_27436]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3207,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 23.98/3.51      | k2_tarski(sK7,sK8) != X0
% 23.98/3.51      | sK5 != sK5
% 23.98/3.51      | sK6 != X1 ),
% 23.98/3.51      inference(resolution_lifted,[status(thm)],[c_1471,c_355]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(c_3208,plain,
% 23.98/3.51      ( ~ r1_orders_2(sK5,sK4(sK5,k2_tarski(sK7,sK8),sK6),sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK7,sK6)
% 23.98/3.51      | ~ r1_orders_2(sK5,sK8,sK6)
% 23.98/3.51      | r1_orders_2(sK5,sK6,sK7)
% 23.98/3.51      | r1_lattice3(sK5,k2_tarski(sK7,sK8),sK6)
% 23.98/3.51      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 23.98/3.51      inference(unflattening,[status(thm)],[c_3207]) ).
% 23.98/3.51  
% 23.98/3.51  cnf(contradiction,plain,
% 23.98/3.51      ( $false ),
% 23.98/3.51      inference(minisat,
% 23.98/3.51                [status(thm)],
% 23.98/3.51                [c_78010,c_41942,c_37632,c_35811,c_28226,c_27485,c_9341,
% 23.98/3.51                 c_6220,c_3208,c_78,c_75,c_24,c_25,c_26]) ).
% 23.98/3.51  
% 23.98/3.51  
% 23.98/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.98/3.51  
% 23.98/3.51  ------                               Statistics
% 23.98/3.51  
% 23.98/3.51  ------ General
% 23.98/3.51  
% 23.98/3.51  abstr_ref_over_cycles:                  0
% 23.98/3.51  abstr_ref_under_cycles:                 0
% 23.98/3.51  gc_basic_clause_elim:                   0
% 23.98/3.51  forced_gc_time:                         0
% 23.98/3.51  parsing_time:                           0.008
% 23.98/3.51  unif_index_cands_time:                  0.
% 23.98/3.51  unif_index_add_time:                    0.
% 23.98/3.51  orderings_time:                         0.
% 23.98/3.51  out_proof_time:                         0.056
% 23.98/3.51  total_time:                             2.959
% 23.98/3.51  num_of_symbols:                         48
% 23.98/3.51  num_of_terms:                           51272
% 23.98/3.51  
% 23.98/3.51  ------ Preprocessing
% 23.98/3.51  
% 23.98/3.51  num_of_splits:                          0
% 23.98/3.51  num_of_split_atoms:                     0
% 23.98/3.51  num_of_reused_defs:                     0
% 23.98/3.51  num_eq_ax_congr_red:                    23
% 23.98/3.51  num_of_sem_filtered_clauses:            1
% 23.98/3.51  num_of_subtypes:                        0
% 23.98/3.51  monotx_restored_types:                  0
% 23.98/3.51  sat_num_of_epr_types:                   0
% 23.98/3.51  sat_num_of_non_cyclic_types:            0
% 23.98/3.51  sat_guarded_non_collapsed_types:        0
% 23.98/3.51  num_pure_diseq_elim:                    0
% 23.98/3.51  simp_replaced_by:                       0
% 23.98/3.51  res_preprocessed:                       129
% 23.98/3.51  prep_upred:                             0
% 23.98/3.51  prep_unflattend:                        399
% 23.98/3.51  smt_new_axioms:                         0
% 23.98/3.51  pred_elim_cands:                        5
% 23.98/3.51  pred_elim:                              3
% 23.98/3.51  pred_elim_cl:                           2
% 23.98/3.51  pred_elim_cycles:                       12
% 23.98/3.51  merged_defs:                            0
% 23.98/3.51  merged_defs_ncl:                        0
% 23.98/3.51  bin_hyper_res:                          0
% 23.98/3.51  prep_cycles:                            4
% 23.98/3.51  pred_elim_time:                         0.101
% 23.98/3.51  splitting_time:                         0.
% 23.98/3.51  sem_filter_time:                        0.
% 23.98/3.51  monotx_time:                            0.
% 23.98/3.51  subtype_inf_time:                       0.
% 23.98/3.51  
% 23.98/3.51  ------ Problem properties
% 23.98/3.51  
% 23.98/3.51  clauses:                                26
% 23.98/3.51  conjectures:                            3
% 23.98/3.51  epr:                                    0
% 23.98/3.51  horn:                                   12
% 23.98/3.51  ground:                                 12
% 23.98/3.51  unary:                                  5
% 23.98/3.51  binary:                                 0
% 23.98/3.51  lits:                                   88
% 23.98/3.51  lits_eq:                                9
% 23.98/3.51  fd_pure:                                0
% 23.98/3.51  fd_pseudo:                              0
% 23.98/3.51  fd_cond:                                0
% 23.98/3.51  fd_pseudo_cond:                         3
% 23.98/3.51  ac_symbols:                             0
% 23.98/3.51  
% 23.98/3.51  ------ Propositional Solver
% 23.98/3.51  
% 23.98/3.51  prop_solver_calls:                      31
% 23.98/3.51  prop_fast_solver_calls:                 4759
% 23.98/3.51  smt_solver_calls:                       0
% 23.98/3.51  smt_fast_solver_calls:                  0
% 23.98/3.51  prop_num_of_clauses:                    22735
% 23.98/3.51  prop_preprocess_simplified:             32102
% 23.98/3.51  prop_fo_subsumed:                       335
% 23.98/3.51  prop_solver_time:                       0.
% 23.98/3.51  smt_solver_time:                        0.
% 23.98/3.51  smt_fast_solver_time:                   0.
% 23.98/3.51  prop_fast_solver_time:                  0.
% 23.98/3.51  prop_unsat_core_time:                   0.003
% 23.98/3.51  
% 23.98/3.51  ------ QBF
% 23.98/3.51  
% 23.98/3.51  qbf_q_res:                              0
% 23.98/3.51  qbf_num_tautologies:                    0
% 23.98/3.51  qbf_prep_cycles:                        0
% 23.98/3.51  
% 23.98/3.51  ------ BMC1
% 23.98/3.51  
% 23.98/3.51  bmc1_current_bound:                     -1
% 23.98/3.51  bmc1_last_solved_bound:                 -1
% 23.98/3.51  bmc1_unsat_core_size:                   -1
% 23.98/3.51  bmc1_unsat_core_parents_size:           -1
% 23.98/3.51  bmc1_merge_next_fun:                    0
% 23.98/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.98/3.51  
% 23.98/3.51  ------ Instantiation
% 23.98/3.51  
% 23.98/3.51  inst_num_of_clauses:                    4259
% 23.98/3.51  inst_num_in_passive:                    1134
% 23.98/3.51  inst_num_in_active:                     1601
% 23.98/3.51  inst_num_in_unprocessed:                1530
% 23.98/3.51  inst_num_of_loops:                      2112
% 23.98/3.51  inst_num_of_learning_restarts:          0
% 23.98/3.51  inst_num_moves_active_passive:          508
% 23.98/3.51  inst_lit_activity:                      0
% 23.98/3.51  inst_lit_activity_moves:                1
% 23.98/3.51  inst_num_tautologies:                   0
% 23.98/3.51  inst_num_prop_implied:                  0
% 23.98/3.51  inst_num_existing_simplified:           0
% 23.98/3.51  inst_num_eq_res_simplified:             0
% 23.98/3.51  inst_num_child_elim:                    0
% 23.98/3.51  inst_num_of_dismatching_blockings:      5537
% 23.98/3.51  inst_num_of_non_proper_insts:           5421
% 23.98/3.51  inst_num_of_duplicates:                 0
% 23.98/3.51  inst_inst_num_from_inst_to_res:         0
% 23.98/3.51  inst_dismatching_checking_time:         0.
% 23.98/3.51  
% 23.98/3.51  ------ Resolution
% 23.98/3.51  
% 23.98/3.51  res_num_of_clauses:                     0
% 23.98/3.51  res_num_in_passive:                     0
% 23.98/3.51  res_num_in_active:                      0
% 23.98/3.51  res_num_of_loops:                       133
% 23.98/3.51  res_forward_subset_subsumed:            510
% 23.98/3.51  res_backward_subset_subsumed:           14
% 23.98/3.51  res_forward_subsumed:                   0
% 23.98/3.51  res_backward_subsumed:                  0
% 23.98/3.51  res_forward_subsumption_resolution:     3
% 23.98/3.51  res_backward_subsumption_resolution:    0
% 23.98/3.51  res_clause_to_clause_subsumption:       27500
% 23.98/3.51  res_orphan_elimination:                 0
% 23.98/3.51  res_tautology_del:                      237
% 23.98/3.51  res_num_eq_res_simplified:              0
% 23.98/3.51  res_num_sel_changes:                    0
% 23.98/3.51  res_moves_from_active_to_pass:          0
% 23.98/3.51  
% 23.98/3.51  ------ Superposition
% 23.98/3.51  
% 23.98/3.51  sup_time_total:                         0.
% 23.98/3.51  sup_time_generating:                    0.
% 23.98/3.51  sup_time_sim_full:                      0.
% 23.98/3.51  sup_time_sim_immed:                     0.
% 23.98/3.51  
% 23.98/3.51  sup_num_of_clauses:                     2205
% 23.98/3.51  sup_num_in_active:                      394
% 23.98/3.51  sup_num_in_passive:                     1811
% 23.98/3.51  sup_num_of_loops:                       422
% 23.98/3.51  sup_fw_superposition:                   976
% 23.98/3.51  sup_bw_superposition:                   2561
% 23.98/3.51  sup_immediate_simplified:               689
% 23.98/3.51  sup_given_eliminated:                   0
% 23.98/3.51  comparisons_done:                       0
% 23.98/3.51  comparisons_avoided:                    194
% 23.98/3.51  
% 23.98/3.51  ------ Simplifications
% 23.98/3.51  
% 23.98/3.51  
% 23.98/3.51  sim_fw_subset_subsumed:                 395
% 23.98/3.51  sim_bw_subset_subsumed:                 50
% 23.98/3.51  sim_fw_subsumed:                        279
% 23.98/3.51  sim_bw_subsumed:                        8
% 23.98/3.51  sim_fw_subsumption_res:                 60
% 23.98/3.51  sim_bw_subsumption_res:                 0
% 23.98/3.51  sim_tautology_del:                      36
% 23.98/3.51  sim_eq_tautology_del:                   1
% 23.98/3.51  sim_eq_res_simp:                        18
% 23.98/3.51  sim_fw_demodulated:                     0
% 23.98/3.51  sim_bw_demodulated:                     0
% 23.98/3.51  sim_light_normalised:                   0
% 23.98/3.51  sim_joinable_taut:                      0
% 23.98/3.51  sim_joinable_simp:                      0
% 23.98/3.51  sim_ac_normalised:                      0
% 23.98/3.51  sim_smt_subsumption:                    0
% 23.98/3.51  
%------------------------------------------------------------------------------
