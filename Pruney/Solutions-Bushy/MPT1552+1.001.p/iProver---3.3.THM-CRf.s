%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:52 EST 2020

% Result     : Theorem 1.27s
% Output     : CNFRefutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  195 (3152 expanded)
%              Number of clauses        :  143 ( 837 expanded)
%              Number of leaves         :   16 ( 910 expanded)
%              Depth                    :   22
%              Number of atoms          : 1002 (29331 expanded)
%              Number of equality atoms :  267 (4057 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X0,X1,X4)
              & r2_lattice3(X0,X2,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X2,X1) )
        & r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | ~ sP0(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X0,X1,X4)
              & r2_lattice3(X0,X2,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X2,X1) )
        & r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | ~ sP0(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ? [X3] :
              ( ~ r1_orders_2(X1,X0,X3)
              & r2_lattice3(X1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_lattice3(X1,X2,X0) )
        & r1_yellow_0(X1,X2)
        & k1_yellow_0(X1,X2) = X0 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK4(X0,X1,X2))
        & r2_lattice3(X1,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ~ r1_orders_2(X1,X0,sK4(X0,X1,X2))
            & r2_lattice3(X1,X2,sK4(X0,X1,X2))
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_lattice3(X1,X2,X0) )
        & r1_yellow_0(X1,X2)
        & k1_yellow_0(X1,X2) = X0 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X1,X2) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) )
                 => ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 ) )
                & ( ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 )
                 => ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) )
                 => ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 ) )
                & ( ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 )
                 => ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X4)
                         => r1_orders_2(X0,X1,X4) ) )
                    & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | sP0(X1,X0,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ~ r1_yellow_0(X0,X2)
              | k1_yellow_0(X0,X2) != X1 )
            & ! [X3] :
                ( r1_orders_2(X0,X1,X3)
                | ~ r2_lattice3(X0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X2,X1) )
          | sP0(X1,X0,X2) )
     => ( ( ( ~ r1_yellow_0(X0,sK7)
            | k1_yellow_0(X0,sK7) != X1 )
          & ! [X3] :
              ( r1_orders_2(X0,X1,X3)
              | ~ r2_lattice3(X0,sK7,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,sK7,X1) )
        | sP0(X1,X0,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | sP0(X1,X0,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != sK6 )
              & ! [X3] :
                  ( r1_orders_2(X0,sK6,X3)
                  | ~ r2_lattice3(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X2,sK6) )
            | sP0(sK6,X0,X2) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r1_yellow_0(X0,X2)
                    | k1_yellow_0(X0,X2) != X1 )
                  & ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | sP0(X1,X0,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(sK5,X2)
                  | k1_yellow_0(sK5,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(sK5,X1,X3)
                    | ~ r2_lattice3(sK5,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
                & r2_lattice3(sK5,X2,X1) )
              | sP0(X1,sK5,X2) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( ( ~ r1_yellow_0(sK5,sK7)
          | k1_yellow_0(sK5,sK7) != sK6 )
        & ! [X3] :
            ( r1_orders_2(sK5,sK6,X3)
            | ~ r2_lattice3(sK5,sK7,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
        & r2_lattice3(sK5,sK7,sK6) )
      | sP0(sK6,sK5,sK7) )
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f13,f30,f29,f28])).

fof(f51,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | sP0(sK6,sK5,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_lattice3(X1,X2,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X3] :
      ( r1_orders_2(sK5,sK6,X3)
      | ~ r2_lattice3(sK5,sK7,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK5))
      | sP0(sK6,sK5,sK7) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X1,X2,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK4(X0,X1,X2))
      | ~ r2_lattice3(X1,X2,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,
    ( ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6
    | sP0(sK6,sK5,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK3(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK3(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK3(X0,X1))
              & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f22,f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f32])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | k1_yellow_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( sP0(sK6,sK5,sK7)
    | r2_lattice3(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_532,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | k1_yellow_0(X0,X1) = X2
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_533,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_2129,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(subtyping,[status(esa)],[c_533])).

cnf(c_2574,plain,
    ( k1_yellow_0(sK5,sK7) = sK6
    | r2_lattice3(sK5,sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2129])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( sP0(sK6,sK5,sK7)
    | ~ r2_lattice3(sK5,sK7,X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_594,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(sK5,sK7,X3)
    | r1_orders_2(sK5,sK6,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | m1_subset_1(sK4(X2,X0,X1),u1_struct_0(X0))
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_595,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_2125,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_595])).

cnf(c_2143,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2125])).

cnf(c_2578,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_2201,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | r2_lattice3(X1,X2,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_633,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK4(X2,X0,X1))
    | ~ r2_lattice3(sK5,sK7,X3)
    | r1_orders_2(sK5,sK6,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_634,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_2123,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_634])).

cnf(c_2144,plain,
    ( r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | ~ r2_lattice3(sK5,sK7,sK6)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2123])).

cnf(c_2206,plain,
    ( r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7)) = iProver_top
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2144])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_lattice3(X1,X2,X0)
    | ~ r1_orders_2(X1,X0,sK4(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_672,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(sK5,sK7,X3)
    | ~ r1_orders_2(X0,X2,sK4(X2,X0,X1))
    | r1_orders_2(sK5,sK6,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_673,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0)
    | ~ r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_2121,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,X0_46)
    | ~ r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_673])).

cnf(c_2145,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2121])).

cnf(c_2209,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2145])).

cnf(c_542,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k1_yellow_0(X1,X2) = X3
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_543,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_2128,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | r1_orders_2(sK5,sK6,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_2806,plain,
    ( ~ r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | ~ m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5))
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2807,plain,
    ( k1_yellow_0(sK5,sK7) = sK6
    | r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7)) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) = iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2806])).

cnf(c_16,negated_conjecture,
    ( sP0(sK6,sK5,sK7)
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_693,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK4(X2,X0,X1))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_694,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_2120,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(subtyping,[status(esa)],[c_694])).

cnf(c_2586,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2152,plain,
    ( X0_46 != X1_46
    | sK4(X0_46,X0_44,X0_45) = sK4(X1_46,X0_44,X0_45) ),
    theory(equality)).

cnf(c_2156,plain,
    ( sK4(sK6,sK5,sK7) = sK4(sK6,sK5,sK7)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_2147,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_2158,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_615,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | m1_subset_1(sK4(X2,X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_616,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_2124,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(subtyping,[status(esa)],[c_616])).

cnf(c_2205,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2124])).

cnf(c_654,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK4(X2,X0,X1))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_655,plain,
    ( r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_2122,plain,
    ( r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7))
    | ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) != sK6 ),
    inference(subtyping,[status(esa)],[c_655])).

cnf(c_2208,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7)) = iProver_top
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_2211,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2120])).

cnf(c_2151,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X0_47)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2829,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | X0_46 != sK6 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_2866,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_yellow_0(sK5,X0_45) != sK6 ),
    inference(instantiation,[status(thm)],[c_2829])).

cnf(c_2867,plain,
    ( k1_yellow_0(sK5,X0_45) != sK6
    | m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2866])).

cnf(c_2869,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_yellow_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_562,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | r1_yellow_0(X0,X1)
    | sK6 != X2
    | sK7 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_563,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | r1_yellow_0(sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_2127,plain,
    ( r2_lattice3(sK5,sK7,sK6)
    | r1_yellow_0(sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_563])).

cnf(c_2576,plain,
    ( r2_lattice3(sK5,sK7,sK6) = iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_564,plain,
    ( r2_lattice3(sK5,sK7,sK6) = iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_307,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_308,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X0,X1),u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_312,plain,
    ( r1_yellow_0(sK5,X0)
    | m1_subset_1(sK2(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_20])).

cnf(c_313,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X0,X1),u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_2137,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X0_45,X0_46),u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_2169,plain,
    ( r2_lattice3(sK5,X0_45,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,X0_45,X0_46),u1_struct_0(sK5)) = iProver_top
    | r1_yellow_0(sK5,X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_2171,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_6,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_331,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_332,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK2(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_336,plain,
    ( r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_lattice3(sK5,X0,sK2(sK5,X0,X1))
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_20])).

cnf(c_337,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK2(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0) ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_2136,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | r2_lattice3(sK5,X0_45,sK2(sK5,X0_45,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_2172,plain,
    ( r2_lattice3(sK5,X0_45,X0_46) != iProver_top
    | r2_lattice3(sK5,X0_45,sK2(sK5,X0_45,X0_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_2174,plain,
    ( r2_lattice3(sK5,sK7,sK2(sK5,sK7,sK6)) = iProver_top
    | r2_lattice3(sK5,sK7,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_5,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_355,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_356,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK2(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( r1_yellow_0(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X1,sK2(sK5,X0,X1))
    | ~ r2_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_20])).

cnf(c_361,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK2(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_2135,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | ~ r1_orders_2(sK5,X0_46,sK2(sK5,X0_45,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | r1_yellow_0(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_2175,plain,
    ( r2_lattice3(sK5,X0_45,X0_46) != iProver_top
    | r1_orders_2(sK5,X0_46,sK2(sK5,X0_45,X0_46)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_2177,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | r1_orders_2(sK5,sK6,sK2(sK5,sK7,sK6)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_572,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_yellow_0(X1,X2)
    | sK6 != X3
    | sK7 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_573,plain,
    ( ~ r2_lattice3(sK5,sK7,X0)
    | r1_orders_2(sK5,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_yellow_0(sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_2126,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | r1_orders_2(sK5,sK6,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | r1_yellow_0(sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_573])).

cnf(c_2811,plain,
    ( ~ r2_lattice3(sK5,sK7,sK2(sK5,X0_45,sK6))
    | r1_orders_2(sK5,sK6,sK2(sK5,X0_45,sK6))
    | ~ m1_subset_1(sK2(sK5,X0_45,sK6),u1_struct_0(sK5))
    | r1_yellow_0(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_2814,plain,
    ( r2_lattice3(sK5,sK7,sK2(sK5,X0_45,sK6)) != iProver_top
    | r1_orders_2(sK5,sK6,sK2(sK5,X0_45,sK6)) = iProver_top
    | m1_subset_1(sK2(sK5,X0_45,sK6),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2811])).

cnf(c_2816,plain,
    ( r2_lattice3(sK5,sK7,sK2(sK5,sK7,sK6)) != iProver_top
    | r1_orders_2(sK5,sK6,sK2(sK5,sK7,sK6)) = iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_2979,plain,
    ( r1_yellow_0(sK5,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_24,c_564,c_2171,c_2174,c_2177,c_2816])).

cnf(c_2149,plain,
    ( ~ r1_orders_2(X0_44,X0_46,X1_46)
    | r1_orders_2(X0_44,X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_2838,plain,
    ( ~ r1_orders_2(sK5,X0_46,X1_46)
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | sK4(sK6,sK5,sK7) != X1_46
    | sK6 != X0_46 ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2901,plain,
    ( ~ r1_orders_2(sK5,X0_46,sK4(sK6,sK5,sK7))
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | sK4(sK6,sK5,sK7) != sK4(sK6,sK5,sK7)
    | sK6 != X0_46 ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_3029,plain,
    ( ~ r1_orders_2(sK5,k1_yellow_0(sK5,X0_45),sK4(sK6,sK5,sK7))
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7))
    | sK4(sK6,sK5,sK7) != sK4(sK6,sK5,sK7)
    | sK6 != k1_yellow_0(sK5,X0_45) ),
    inference(instantiation,[status(thm)],[c_2901])).

cnf(c_3031,plain,
    ( sK4(sK6,sK5,sK7) != sK4(sK6,sK5,sK7)
    | sK6 != k1_yellow_0(sK5,X0_45)
    | r1_orders_2(sK5,k1_yellow_0(sK5,X0_45),sK4(sK6,sK5,sK7)) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3029])).

cnf(c_3033,plain,
    ( sK4(sK6,sK5,sK7) != sK4(sK6,sK5,sK7)
    | sK6 != k1_yellow_0(sK5,sK7)
    | r1_orders_2(sK5,k1_yellow_0(sK5,sK7),sK4(sK6,sK5,sK7)) != iProver_top
    | r1_orders_2(sK5,sK6,sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_420,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_421,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,k1_yellow_0(sK5,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_2133,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | r1_orders_2(sK5,k1_yellow_0(sK5,X0_45),X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | ~ m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_3030,plain,
    ( ~ r2_lattice3(sK5,X0_45,sK4(sK6,sK5,sK7))
    | r1_orders_2(sK5,k1_yellow_0(sK5,X0_45),sK4(sK6,sK5,sK7))
    | ~ m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5))
    | ~ m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_3035,plain,
    ( r2_lattice3(sK5,X0_45,sK4(sK6,sK5,sK7)) != iProver_top
    | r1_orders_2(sK5,k1_yellow_0(sK5,X0_45),sK4(sK6,sK5,sK7)) = iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3030])).

cnf(c_3037,plain,
    ( r2_lattice3(sK5,sK7,sK4(sK6,sK5,sK7)) != iProver_top
    | r1_orders_2(sK5,k1_yellow_0(sK5,sK7),sK4(sK6,sK5,sK7)) = iProver_top
    | m1_subset_1(sK4(sK6,sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_2148,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_3150,plain,
    ( k1_yellow_0(sK5,X0_45) != X0_46
    | sK6 != X0_46
    | sK6 = k1_yellow_0(sK5,X0_45) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_3151,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | sK6 = k1_yellow_0(sK5,sK7)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3150])).

cnf(c_3160,plain,
    ( k1_yellow_0(sK5,sK7) != sK6
    | r2_lattice3(sK5,sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_24,c_564,c_2156,c_2158,c_2171,c_2174,c_2177,c_2205,c_2208,c_2211,c_2816,c_2869,c_3033,c_3037,c_3151])).

cnf(c_3204,plain,
    ( r2_lattice3(sK5,sK7,sK6) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2578,c_2201,c_2206,c_2209,c_2807,c_3160])).

cnf(c_3210,plain,
    ( k1_yellow_0(sK5,sK7) = sK6
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_3204])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_441,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_442,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0,X1),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0)
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_2132,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_45,X0_46),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45)
    | k1_yellow_0(sK5,X0_45) = X0_46 ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_2185,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | m1_subset_1(sK1(sK5,sK7,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_0,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_483,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_484,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,X1,sK1(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0)
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_2130,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | ~ r1_orders_2(sK5,X0_46,sK1(sK5,X0_45,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45)
    | k1_yellow_0(sK5,X0_45) = X0_46 ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_2191,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | ~ r1_orders_2(sK5,sK6,sK1(sK5,sK7,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_2981,plain,
    ( r1_yellow_0(sK5,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2979])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_462,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK1(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | k1_yellow_0(X0,X1) = X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_463,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r2_lattice3(sK5,X0,sK1(sK5,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0)
    | k1_yellow_0(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_2131,plain,
    ( ~ r2_lattice3(sK5,X0_45,X0_46)
    | r2_lattice3(sK5,X0_45,sK1(sK5,X0_45,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45)
    | k1_yellow_0(sK5,X0_45) = X0_46 ),
    inference(subtyping,[status(esa)],[c_463])).

cnf(c_2572,plain,
    ( k1_yellow_0(sK5,X0_45) = X0_46
    | r2_lattice3(sK5,X0_45,X0_46) != iProver_top
    | r2_lattice3(sK5,X0_45,sK1(sK5,X0_45,X0_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2131])).

cnf(c_2575,plain,
    ( k1_yellow_0(sK5,sK7) = sK6
    | r2_lattice3(sK5,sK7,X0_46) != iProver_top
    | r1_orders_2(sK5,sK6,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_3425,plain,
    ( k1_yellow_0(sK5,sK7) = X0_46
    | k1_yellow_0(sK5,sK7) = sK6
    | r2_lattice3(sK5,sK7,X0_46) != iProver_top
    | r1_orders_2(sK5,sK6,sK1(sK5,sK7,X0_46)) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,sK7,X0_46),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_2575])).

cnf(c_3455,plain,
    ( ~ r2_lattice3(sK5,sK7,X0_46)
    | r1_orders_2(sK5,sK6,sK1(sK5,sK7,X0_46))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK5,sK7,X0_46),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) = X0_46
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3425])).

cnf(c_3457,plain,
    ( ~ r2_lattice3(sK5,sK7,sK6)
    | r1_orders_2(sK5,sK6,sK1(sK5,sK7,sK6))
    | ~ m1_subset_1(sK1(sK5,sK7,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,sK7)
    | k1_yellow_0(sK5,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_3455])).

cnf(c_3461,plain,
    ( k1_yellow_0(sK5,sK7) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_19,c_2185,c_2191,c_2129,c_2981,c_3457])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_405,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_406,plain,
    ( r2_lattice3(sK5,X0,k1_yellow_0(sK5,X0))
    | ~ m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_2134,plain,
    ( r2_lattice3(sK5,X0_45,k1_yellow_0(sK5,X0_45))
    | ~ m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5))
    | ~ r1_yellow_0(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_2569,plain,
    ( r2_lattice3(sK5,X0_45,k1_yellow_0(sK5,X0_45)) = iProver_top
    | m1_subset_1(k1_yellow_0(sK5,X0_45),u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_3476,plain,
    ( r2_lattice3(sK5,sK7,k1_yellow_0(sK5,sK7)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_2569])).

cnf(c_3480,plain,
    ( r2_lattice3(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r1_yellow_0(sK5,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3476,c_3461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3480,c_3461,c_3160,c_2979,c_24])).


%------------------------------------------------------------------------------
