%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:17 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :  214 (1213 expanded)
%              Number of clauses        :  141 ( 295 expanded)
%              Number of leaves         :   19 ( 378 expanded)
%              Depth                    :   32
%              Number of atoms          : 1124 (9818 expanded)
%              Number of equality atoms :  110 ( 248 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK3(X0,X1,X2),X2)
        & r3_lattices(X1,X5,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,sK2(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X2)
            & r3_lattices(X1,sK2(X0,X1,X2),sK3(X0,X1,X2))
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r2_hidden(sK7(X3),X2)
        & r3_lattices(X0,X3,sK7(X3))
        & m1_subset_1(sK7(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
     => ( ~ r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,sK6)
                & r3_lattices(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,sK5)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
            & ! [X3] :
                ( ? [X4] :
                    ( r2_hidden(X4,X2)
                    & r3_lattices(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK4,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK4)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK4)) ) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    & ! [X3] :
        ( ( r2_hidden(sK7(X3),sK6)
          & r3_lattices(sK4,X3,sK7(X3))
          & m1_subset_1(sK7(X3),u1_struct_0(sK4)) )
        | ~ r2_hidden(X3,sK5)
        | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f46,f45,f44])).

fof(f74,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f77,plain,(
    ! [X3] :
      ( r3_lattices(sK4,X3,sK7(X3))
      | ~ r2_hidden(X3,sK5)
      | ~ m1_subset_1(X3,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X3] :
      ( m1_subset_1(sK7(X3),u1_struct_0(sK4))
      | ~ r2_hidden(X3,sK5)
      | ~ m1_subset_1(X3,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK6)
      | ~ r2_hidden(X3,sK5)
      | ~ m1_subset_1(X3,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK1(X0,X1,X2))
        & r4_lattice3(X0,sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK1(X0,X1,X2))
                & r4_lattice3(X0,sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f79,plain,(
    ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1804,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1802,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2874,plain,
    ( X0_54 != X1_54
    | X1_54 = X0_54 ),
    inference(resolution,[status(thm)],[c_1804,c_1802])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_632,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_633,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_637,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_31,c_30,c_28])).

cnf(c_1787,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | sK2(X0_54,sK4,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_637])).

cnf(c_3797,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | X0_54 = sK2(X0_54,sK4,X0_55) ),
    inference(resolution,[status(thm)],[c_2874,c_1787])).

cnf(c_1810,plain,
    ( ~ r2_hidden(X0_54,X0_55)
    | r2_hidden(X1_54,X0_55)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_4192,plain,
    ( r2_hidden(X0_54,X0_55)
    | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
    | ~ r2_hidden(sK2(X0_54,sK4,X1_55),X0_55) ),
    inference(resolution,[status(thm)],[c_3797,c_1810])).

cnf(c_16,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_5_lattice3(X0,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_491,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_5_lattice3(X0,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_492,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_31,c_30,c_28])).

cnf(c_497,plain,
    ( ~ r3_lattices(sK4,X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_1792,plain,
    ( ~ r3_lattices(sK4,X0_54,X1_54)
    | ~ r2_hidden(X1_54,X0_55)
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_26,negated_conjecture,
    ( r3_lattices(sK4,X0,sK7(X0))
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1798,negated_conjecture,
    ( r3_lattices(sK4,X0_54,sK7(X0_54))
    | ~ r2_hidden(X0_54,sK5)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3607,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | ~ r2_hidden(X0_54,sK5)
    | ~ r2_hidden(sK7(X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_1792,c_1798])).

cnf(c_2275,plain,
    ( r3_lattices(sK4,X0_54,sK7(X0_54)) = iProver_top
    | r2_hidden(X0_54,sK5) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_2279,plain,
    ( r3_lattices(sK4,X0_54,X1_54) != iProver_top
    | r2_hidden(X1_54,X0_55) != iProver_top
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_3552,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
    | r2_hidden(X0_54,sK5) != iProver_top
    | r2_hidden(sK7(X0_54),X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_2279])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK7(X0),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1797,negated_conjecture,
    ( ~ r2_hidden(X0_54,sK5)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1826,plain,
    ( r2_hidden(X0_54,sK5) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1797])).

cnf(c_3877,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK7(X0_54),X0_55) != iProver_top
    | r2_hidden(X0_54,sK5) != iProver_top
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3552,c_1826])).

cnf(c_3878,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
    | r2_hidden(X0_54,sK5) != iProver_top
    | r2_hidden(sK7(X0_54),X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3877])).

cnf(c_3879,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | ~ r2_hidden(X0_54,sK5)
    | ~ r2_hidden(sK7(X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3878])).

cnf(c_3915,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r2_hidden(sK7(X0_54),X0_55)
    | ~ r2_hidden(X0_54,sK5)
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3607,c_3879])).

cnf(c_3916,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | ~ r2_hidden(X0_54,sK5)
    | ~ r2_hidden(sK7(X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_3915])).

cnf(c_7136,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
    | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
    | ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55)
    | ~ m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_4192,c_3916])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_615,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_619,plain,
    ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_31,c_30,c_28])).

cnf(c_620,plain,
    ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_1788,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_18779,plain,
    ( ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55)
    | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
    | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7136,c_1788])).

cnf(c_18780,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
    | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
    | ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55) ),
    inference(renaming,[status(thm)],[c_18779])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1799,negated_conjecture,
    ( ~ r2_hidden(X0_54,sK5)
    | r2_hidden(sK7(X0_54),sK6)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_18874,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
    | ~ m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_18780,c_1799])).

cnf(c_18879,plain,
    ( ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18874,c_1788])).

cnf(c_18880,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5) ),
    inference(renaming,[status(thm)],[c_18879])).

cnf(c_3004,plain,
    ( ~ r2_hidden(X0_54,X0_55)
    | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
    | r2_hidden(sK2(X0_54,sK4,X1_55),X0_55) ),
    inference(resolution,[status(thm)],[c_1787,c_1810])).

cnf(c_18901,plain,
    ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
    | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(X0_54,sK5) ),
    inference(resolution,[status(thm)],[c_18880,c_3004])).

cnf(c_19248,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(X0_54,sK5)
    | ~ r2_hidden(sK7(X0_54),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_18901,c_3916])).

cnf(c_19297,plain,
    ( r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
    | ~ r2_hidden(X0_54,sK5)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_19248,c_1799])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_804,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_805,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_28])).

cnf(c_810,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_809])).

cnf(c_1781,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r1_lattices(sK4,X1_54,X0_54)
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_810])).

cnf(c_14,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_15,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_198,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_436,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_198,c_29])).

cnf(c_437,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_31,c_30,c_28])).

cnf(c_1796,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_3459,plain,
    ( r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_1781,c_1796])).

cnf(c_789,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_790,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_28])).

cnf(c_1782,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_794])).

cnf(c_5134,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r2_hidden(X0_54,X0_55)
    | r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3459,c_1782])).

cnf(c_5135,plain,
    ( r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_5134])).

cnf(c_6,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_873,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_874,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_878,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_874,c_28])).

cnf(c_879,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_878])).

cnf(c_1778,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r1_lattices(sK4,sK0(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_879])).

cnf(c_5156,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55)
    | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_5135,c_1778])).

cnf(c_8,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_831,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_31])).

cnf(c_832,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_836,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_28])).

cnf(c_837,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_836])).

cnf(c_1780,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_837])).

cnf(c_2496,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_11486,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_1782,c_2496])).

cnf(c_19319,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55)
    | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55),sK5)
    | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_19297,c_11486])).

cnf(c_19321,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
    | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),sK5)
    | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_19319])).

cnf(c_7,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_852,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_853,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_857,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_28])).

cnf(c_858,plain,
    ( r4_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_857])).

cnf(c_1779,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_858])).

cnf(c_2517,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X1_55)
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_6633,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),sK5)
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_6634,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_6182,plain,
    ( m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_1809,plain,
    ( ~ r4_lattice3(X0_53,X0_54,X0_55)
    | r4_lattice3(X0_53,X1_54,X0_55)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2614,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r4_lattice3(sK4,k15_lattice3(sK4,X1_55),X0_55)
    | X0_54 != k15_lattice3(sK4,X1_55) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_2724,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | r4_lattice3(sK4,k15_lattice3(sK4,X2_55),X1_55)
    | k15_lattice3(sK4,X2_55) != k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2614])).

cnf(c_3413,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),sK5)
    | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2724])).

cnf(c_5082,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
    | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3413])).

cnf(c_23,plain,
    ( ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_451,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_452,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_456,plain,
    ( k15_lattice3(sK4,a_2_5_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_31,c_30,c_28])).

cnf(c_1795,plain,
    ( k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
    inference(subtyping,[status(esa)],[c_456])).

cnf(c_4379,plain,
    ( k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) = k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2734,plain,
    ( k15_lattice3(sK4,X0_55) = k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_4039,plain,
    ( k15_lattice3(sK4,sK6) = k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_2603,plain,
    ( X0_54 != X1_54
    | X0_54 = k15_lattice3(sK4,X0_55)
    | k15_lattice3(sK4,X0_55) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_2711,plain,
    ( X0_54 != k15_lattice3(sK4,X0_55)
    | X0_54 = k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55))
    | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) != k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_2804,plain,
    ( k15_lattice3(sK4,X0_55) != k15_lattice3(sK4,X0_55)
    | k15_lattice3(sK4,X0_55) = k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55))
    | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) != k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2711])).

cnf(c_3510,plain,
    ( k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) != k15_lattice3(sK4,sK6)
    | k15_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6))
    | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_2804])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_518,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_519,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_523,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_31,c_30,c_28])).

cnf(c_524,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_523])).

cnf(c_895,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_794,c_524])).

cnf(c_1777,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | r1_lattices(sK4,k15_lattice3(sK4,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_895])).

cnf(c_2605,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | r1_lattices(sK4,k15_lattice3(sK4,X1_55),k15_lattice3(sK4,X0_55))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_2975,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_2796,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_24,negated_conjecture,
    ( ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_388,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_4])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_392,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_2,c_1])).

cnf(c_731,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_30])).

cnf(c_732,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_736,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_31,c_28])).

cnf(c_969,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k15_lattice3(sK4,sK6) != X1
    | k15_lattice3(sK4,sK5) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_736])).

cnf(c_970,plain,
    ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_978,plain,
    ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_970,c_794,c_794])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19321,c_6633,c_6634,c_6182,c_5082,c_4379,c_4039,c_3510,c_2975,c_2796,c_978])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:29:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.34/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/1.48  
% 7.34/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.48  
% 7.34/1.48  ------  iProver source info
% 7.34/1.48  
% 7.34/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.48  git: non_committed_changes: false
% 7.34/1.48  git: last_make_outside_of_git: false
% 7.34/1.48  
% 7.34/1.48  ------ 
% 7.34/1.48  ------ Parsing...
% 7.34/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.48  
% 7.34/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.34/1.48  
% 7.34/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.48  
% 7.34/1.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.48  ------ Proving...
% 7.34/1.48  ------ Problem Properties 
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  clauses                                 24
% 7.34/1.48  conjectures                             4
% 7.34/1.48  EPR                                     0
% 7.34/1.48  Horn                                    20
% 7.34/1.48  unary                                   5
% 7.34/1.48  binary                                  5
% 7.34/1.48  lits                                    66
% 7.34/1.48  lits eq                                 6
% 7.34/1.48  fd_pure                                 0
% 7.34/1.48  fd_pseudo                               0
% 7.34/1.48  fd_cond                                 0
% 7.34/1.48  fd_pseudo_cond                          3
% 7.34/1.48  AC symbols                              0
% 7.34/1.48  
% 7.34/1.48  ------ Input Options Time Limit: Unbounded
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  ------ 
% 7.34/1.48  Current options:
% 7.34/1.48  ------ 
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  ------ Proving...
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  % SZS status Theorem for theBenchmark.p
% 7.34/1.48  
% 7.34/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.48  
% 7.34/1.48  fof(f6,axiom,(
% 7.34/1.48    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f23,plain,(
% 7.34/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 7.34/1.48    inference(ennf_transformation,[],[f6])).
% 7.34/1.48  
% 7.34/1.48  fof(f24,plain,(
% 7.34/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.34/1.48    inference(flattening,[],[f23])).
% 7.34/1.48  
% 7.34/1.48  fof(f39,plain,(
% 7.34/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.34/1.48    inference(nnf_transformation,[],[f24])).
% 7.34/1.48  
% 7.34/1.48  fof(f40,plain,(
% 7.34/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.34/1.48    inference(rectify,[],[f39])).
% 7.34/1.48  
% 7.34/1.48  fof(f42,plain,(
% 7.34/1.48    ( ! [X5] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK3(X0,X1,X2),X2) & r3_lattices(X1,X5,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))) )),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f41,plain,(
% 7.34/1.48    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK2(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f43,plain,(
% 7.34/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK3(X0,X1,X2),X2) & r3_lattices(X1,sK2(X0,X1,X2),sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 7.34/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 7.34/1.48  
% 7.34/1.48  fof(f65,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f43])).
% 7.34/1.48  
% 7.34/1.48  fof(f8,conjecture,(
% 7.34/1.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f9,negated_conjecture,(
% 7.34/1.48    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 7.34/1.48    inference(negated_conjecture,[],[f8])).
% 7.34/1.48  
% 7.34/1.48  fof(f27,plain,(
% 7.34/1.48    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f9])).
% 7.34/1.48  
% 7.34/1.48  fof(f28,plain,(
% 7.34/1.48    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f27])).
% 7.34/1.48  
% 7.34/1.48  fof(f46,plain,(
% 7.34/1.48    ( ! [X2,X0] : (! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r2_hidden(sK7(X3),X2) & r3_lattices(X0,X3,sK7(X3)) & m1_subset_1(sK7(X3),u1_struct_0(X0))))) )),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f45,plain,(
% 7.34/1.48    ( ! [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) => (~r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6)) & ! [X3] : (? [X4] : (r2_hidden(X4,sK6) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,u1_struct_0(X0))))) )),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f44,plain,(
% 7.34/1.48    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK4,X3,X4) & m1_subset_1(X4,u1_struct_0(sK4))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK4)))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f47,plain,(
% 7.34/1.48    (~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) & ! [X3] : ((r2_hidden(sK7(X3),sK6) & r3_lattices(sK4,X3,sK7(X3)) & m1_subset_1(sK7(X3),u1_struct_0(sK4))) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,u1_struct_0(sK4)))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 7.34/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f46,f45,f44])).
% 7.34/1.48  
% 7.34/1.48  fof(f74,plain,(
% 7.34/1.48    v4_lattice3(sK4)),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f72,plain,(
% 7.34/1.48    ~v2_struct_0(sK4)),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f73,plain,(
% 7.34/1.48    v10_lattices(sK4)),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f75,plain,(
% 7.34/1.48    l3_lattices(sK4)),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f69,plain,(
% 7.34/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f43])).
% 7.34/1.48  
% 7.34/1.48  fof(f82,plain,(
% 7.34/1.48    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.34/1.48    inference(equality_resolution,[],[f69])).
% 7.34/1.48  
% 7.34/1.48  fof(f77,plain,(
% 7.34/1.48    ( ! [X3] : (r3_lattices(sK4,X3,sK7(X3)) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,u1_struct_0(sK4))) )),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f76,plain,(
% 7.34/1.48    ( ! [X3] : (m1_subset_1(sK7(X3),u1_struct_0(sK4)) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,u1_struct_0(sK4))) )),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f64,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f43])).
% 7.34/1.48  
% 7.34/1.48  fof(f78,plain,(
% 7.34/1.48    ( ! [X3] : (r2_hidden(sK7(X3),sK6) | ~r2_hidden(X3,sK5) | ~m1_subset_1(X3,u1_struct_0(sK4))) )),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f3,axiom,(
% 7.34/1.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f17,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f3])).
% 7.34/1.48  
% 7.34/1.48  fof(f18,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f17])).
% 7.34/1.48  
% 7.34/1.48  fof(f30,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(nnf_transformation,[],[f18])).
% 7.34/1.48  
% 7.34/1.48  fof(f31,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(rectify,[],[f30])).
% 7.34/1.48  
% 7.34/1.48  fof(f32,plain,(
% 7.34/1.48    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f33,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.34/1.48  
% 7.34/1.48  fof(f54,plain,(
% 7.34/1.48    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f33])).
% 7.34/1.48  
% 7.34/1.48  fof(f4,axiom,(
% 7.34/1.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f19,plain,(
% 7.34/1.48    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f4])).
% 7.34/1.48  
% 7.34/1.48  fof(f20,plain,(
% 7.34/1.48    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f19])).
% 7.34/1.48  
% 7.34/1.48  fof(f34,plain,(
% 7.34/1.48    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(nnf_transformation,[],[f20])).
% 7.34/1.48  
% 7.34/1.48  fof(f35,plain,(
% 7.34/1.48    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f34])).
% 7.34/1.48  
% 7.34/1.48  fof(f36,plain,(
% 7.34/1.48    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(rectify,[],[f35])).
% 7.34/1.48  
% 7.34/1.48  fof(f37,plain,(
% 7.34/1.48    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 7.34/1.48    introduced(choice_axiom,[])).
% 7.34/1.48  
% 7.34/1.48  fof(f38,plain,(
% 7.34/1.48    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 7.34/1.48  
% 7.34/1.48  fof(f58,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f38])).
% 7.34/1.48  
% 7.34/1.48  fof(f81,plain,(
% 7.34/1.48    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(equality_resolution,[],[f58])).
% 7.34/1.48  
% 7.34/1.48  fof(f5,axiom,(
% 7.34/1.48    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f21,plain,(
% 7.34/1.48    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f5])).
% 7.34/1.48  
% 7.34/1.48  fof(f22,plain,(
% 7.34/1.48    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f21])).
% 7.34/1.48  
% 7.34/1.48  fof(f63,plain,(
% 7.34/1.48    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f22])).
% 7.34/1.48  
% 7.34/1.48  fof(f57,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK0(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f33])).
% 7.34/1.48  
% 7.34/1.48  fof(f55,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f33])).
% 7.34/1.48  
% 7.34/1.48  fof(f56,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f33])).
% 7.34/1.48  
% 7.34/1.48  fof(f7,axiom,(
% 7.34/1.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f25,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f7])).
% 7.34/1.48  
% 7.34/1.48  fof(f26,plain,(
% 7.34/1.48    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f25])).
% 7.34/1.48  
% 7.34/1.48  fof(f70,plain,(
% 7.34/1.48    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f26])).
% 7.34/1.48  
% 7.34/1.48  fof(f59,plain,(
% 7.34/1.48    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f38])).
% 7.34/1.48  
% 7.34/1.48  fof(f80,plain,(
% 7.34/1.48    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(equality_resolution,[],[f59])).
% 7.34/1.48  
% 7.34/1.48  fof(f79,plain,(
% 7.34/1.48    ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))),
% 7.34/1.48    inference(cnf_transformation,[],[f47])).
% 7.34/1.48  
% 7.34/1.48  fof(f1,axiom,(
% 7.34/1.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f10,plain,(
% 7.34/1.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.34/1.48    inference(pure_predicate_removal,[],[f1])).
% 7.34/1.48  
% 7.34/1.48  fof(f11,plain,(
% 7.34/1.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.34/1.48    inference(pure_predicate_removal,[],[f10])).
% 7.34/1.48  
% 7.34/1.48  fof(f12,plain,(
% 7.34/1.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 7.34/1.48    inference(pure_predicate_removal,[],[f11])).
% 7.34/1.48  
% 7.34/1.48  fof(f13,plain,(
% 7.34/1.48    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.34/1.48    inference(ennf_transformation,[],[f12])).
% 7.34/1.48  
% 7.34/1.48  fof(f14,plain,(
% 7.34/1.48    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.34/1.48    inference(flattening,[],[f13])).
% 7.34/1.48  
% 7.34/1.48  fof(f51,plain,(
% 7.34/1.48    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f14])).
% 7.34/1.48  
% 7.34/1.48  fof(f2,axiom,(
% 7.34/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 7.34/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.48  
% 7.34/1.48  fof(f15,plain,(
% 7.34/1.48    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.34/1.48    inference(ennf_transformation,[],[f2])).
% 7.34/1.48  
% 7.34/1.48  fof(f16,plain,(
% 7.34/1.48    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(flattening,[],[f15])).
% 7.34/1.48  
% 7.34/1.48  fof(f29,plain,(
% 7.34/1.48    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.34/1.48    inference(nnf_transformation,[],[f16])).
% 7.34/1.48  
% 7.34/1.48  fof(f53,plain,(
% 7.34/1.48    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f29])).
% 7.34/1.48  
% 7.34/1.48  fof(f49,plain,(
% 7.34/1.48    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f14])).
% 7.34/1.48  
% 7.34/1.48  fof(f50,plain,(
% 7.34/1.48    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.34/1.48    inference(cnf_transformation,[],[f14])).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1804,plain,
% 7.34/1.48      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 7.34/1.48      theory(equality) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1802,plain,( X0_54 = X0_54 ),theory(equality) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2874,plain,
% 7.34/1.48      ( X0_54 != X1_54 | X1_54 = X0_54 ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_1804,c_1802]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_20,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
% 7.34/1.48      | ~ v4_lattice3(X1)
% 7.34/1.48      | ~ l3_lattices(X1)
% 7.34/1.48      | v2_struct_0(X1)
% 7.34/1.48      | ~ v10_lattices(X1)
% 7.34/1.48      | sK2(X0,X1,X2) = X0 ),
% 7.34/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_29,negated_conjecture,
% 7.34/1.48      ( v4_lattice3(sK4) ),
% 7.34/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_632,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
% 7.34/1.48      | ~ l3_lattices(X1)
% 7.34/1.48      | v2_struct_0(X1)
% 7.34/1.48      | ~ v10_lattices(X1)
% 7.34/1.48      | sK2(X0,X1,X2) = X0
% 7.34/1.48      | sK4 != X1 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_633,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4)
% 7.34/1.48      | sK2(X0,sK4,X1) = X0 ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_632]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_31,negated_conjecture,
% 7.34/1.48      ( ~ v2_struct_0(sK4) ),
% 7.34/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_30,negated_conjecture,
% 7.34/1.48      ( v10_lattices(sK4) ),
% 7.34/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_28,negated_conjecture,
% 7.34/1.48      ( l3_lattices(sK4) ),
% 7.34/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_637,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1)) | sK2(X0,sK4,X1) = X0 ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_633,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1787,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | sK2(X0_54,sK4,X0_55) = X0_54 ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_637]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3797,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | X0_54 = sK2(X0_54,sK4,X0_55) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_2874,c_1787]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1810,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,X0_55)
% 7.34/1.48      | r2_hidden(X1_54,X0_55)
% 7.34/1.48      | X1_54 != X0_54 ),
% 7.34/1.48      theory(equality) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_4192,plain,
% 7.34/1.48      ( r2_hidden(X0_54,X0_55)
% 7.34/1.48      | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X1_55),X0_55) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_3797,c_1810]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_16,plain,
% 7.34/1.48      ( ~ r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ r2_hidden(X2,X3)
% 7.34/1.48      | r2_hidden(X1,a_2_5_lattice3(X0,X3))
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ v4_lattice3(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_491,plain,
% 7.34/1.48      ( ~ r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ r2_hidden(X2,X3)
% 7.34/1.48      | r2_hidden(X1,a_2_5_lattice3(X0,X3))
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_492,plain,
% 7.34/1.48      ( ~ r3_lattices(sK4,X0,X1)
% 7.34/1.48      | ~ r2_hidden(X1,X2)
% 7.34/1.48      | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_491]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_496,plain,
% 7.34/1.48      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
% 7.34/1.48      | ~ r2_hidden(X1,X2)
% 7.34/1.48      | ~ r3_lattices(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_492,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_497,plain,
% 7.34/1.48      ( ~ r3_lattices(sK4,X0,X1)
% 7.34/1.48      | ~ r2_hidden(X1,X2)
% 7.34/1.48      | r2_hidden(X0,a_2_5_lattice3(sK4,X2))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_496]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1792,plain,
% 7.34/1.48      ( ~ r3_lattices(sK4,X0_54,X1_54)
% 7.34/1.48      | ~ r2_hidden(X1_54,X0_55)
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_497]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_26,negated_conjecture,
% 7.34/1.48      ( r3_lattices(sK4,X0,sK7(X0))
% 7.34/1.48      | ~ r2_hidden(X0,sK5)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1798,negated_conjecture,
% 7.34/1.48      ( r3_lattices(sK4,X0_54,sK7(X0_54))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_26]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3607,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(X0_54),X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_1792,c_1798]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2275,plain,
% 7.34/1.48      ( r3_lattices(sK4,X0_54,sK7(X0_54)) = iProver_top
% 7.34/1.48      | r2_hidden(X0_54,sK5) != iProver_top
% 7.34/1.48      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 7.34/1.48      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2279,plain,
% 7.34/1.48      ( r3_lattices(sK4,X0_54,X1_54) != iProver_top
% 7.34/1.48      | r2_hidden(X1_54,X0_55) != iProver_top
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
% 7.34/1.48      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 7.34/1.48      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top ),
% 7.34/1.48      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3552,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
% 7.34/1.48      | r2_hidden(X0_54,sK5) != iProver_top
% 7.34/1.48      | r2_hidden(sK7(X0_54),X0_55) != iProver_top
% 7.34/1.48      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 7.34/1.48      | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) != iProver_top ),
% 7.34/1.48      inference(superposition,[status(thm)],[c_2275,c_2279]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_27,negated_conjecture,
% 7.34/1.48      ( ~ r2_hidden(X0,sK5)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | m1_subset_1(sK7(X0),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1797,negated_conjecture,
% 7.34/1.48      ( ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1826,plain,
% 7.34/1.48      ( r2_hidden(X0_54,sK5) != iProver_top
% 7.34/1.48      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 7.34/1.48      | m1_subset_1(sK7(X0_54),u1_struct_0(sK4)) = iProver_top ),
% 7.34/1.48      inference(predicate_to_equality,[status(thm)],[c_1797]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3877,plain,
% 7.34/1.48      ( m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 7.34/1.48      | r2_hidden(sK7(X0_54),X0_55) != iProver_top
% 7.34/1.48      | r2_hidden(X0_54,sK5) != iProver_top
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_3552,c_1826]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3878,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) = iProver_top
% 7.34/1.48      | r2_hidden(X0_54,sK5) != iProver_top
% 7.34/1.48      | r2_hidden(sK7(X0_54),X0_55) != iProver_top
% 7.34/1.48      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_3877]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3879,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(X0_54),X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_3878]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3915,plain,
% 7.34/1.48      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ r2_hidden(sK7(X0_54),X0_55)
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_3607,c_3879]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3916,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(X0_54),X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_3915]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_7136,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55)
% 7.34/1.48      | ~ m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_4192,c_3916]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_21,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
% 7.34/1.48      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 7.34/1.48      | ~ v4_lattice3(X1)
% 7.34/1.48      | ~ l3_lattices(X1)
% 7.34/1.48      | v2_struct_0(X1)
% 7.34/1.48      | ~ v10_lattices(X1) ),
% 7.34/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_614,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
% 7.34/1.48      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 7.34/1.48      | ~ l3_lattices(X1)
% 7.34/1.48      | v2_struct_0(X1)
% 7.34/1.48      | ~ v10_lattices(X1)
% 7.34/1.48      | sK4 != X1 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_615,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
% 7.34/1.48      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_614]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_619,plain,
% 7.34/1.48      ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_615,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_620,plain,
% 7.34/1.48      ( ~ r2_hidden(X0,a_2_5_lattice3(sK4,X1))
% 7.34/1.48      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_619]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1788,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_620]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18779,plain,
% 7.34/1.48      ( ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55)
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_7136,c_1788]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18780,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(sK2(X0_54,sK4,X0_55)),X1_55) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_18779]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_25,negated_conjecture,
% 7.34/1.48      ( ~ r2_hidden(X0,sK5)
% 7.34/1.48      | r2_hidden(sK7(X0),sK6)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1799,negated_conjecture,
% 7.34/1.48      ( ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | r2_hidden(sK7(X0_54),sK6)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_25]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18874,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
% 7.34/1.48      | ~ m1_subset_1(sK2(X0_54,sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_18780,c_1799]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18879,plain,
% 7.34/1.48      ( ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5)
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_18874,c_1788]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18880,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(sK2(X0_54,sK4,X0_55),sK5) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_18879]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3004,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,X0_55)
% 7.34/1.48      | ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X1_55))
% 7.34/1.48      | r2_hidden(sK2(X0_54,sK4,X1_55),X0_55) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_1787,c_1810]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_18901,plain,
% 7.34/1.48      ( ~ r2_hidden(X0_54,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_18880,c_3004]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_19248,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ r2_hidden(sK7(X0_54),X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_18901,c_3916]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_19297,plain,
% 7.34/1.48      ( r2_hidden(X0_54,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | ~ r2_hidden(X0_54,sK5)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_19248,c_1799]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_9,plain,
% 7.34/1.48      ( ~ r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r1_lattices(X0,X3,X1)
% 7.34/1.48      | ~ r2_hidden(X3,X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_804,plain,
% 7.34/1.48      ( ~ r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r1_lattices(X0,X3,X1)
% 7.34/1.48      | ~ r2_hidden(X3,X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_805,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r1_lattices(sK4,X2,X0)
% 7.34/1.48      | ~ r2_hidden(X2,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_804]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_809,plain,
% 7.34/1.48      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ r2_hidden(X2,X1)
% 7.34/1.48      | r1_lattices(sK4,X2,X0)
% 7.34/1.48      | ~ r4_lattice3(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_805,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_810,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r1_lattices(sK4,X2,X0)
% 7.34/1.48      | ~ r2_hidden(X2,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_809]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1781,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | r1_lattices(sK4,X1_54,X0_54)
% 7.34/1.48      | ~ r2_hidden(X1_54,X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_810]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_14,plain,
% 7.34/1.48      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.34/1.48      | ~ v4_lattice3(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_15,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_198,plain,
% 7.34/1.48      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 7.34/1.48      | ~ v4_lattice3(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_14,c_15]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_436,plain,
% 7.34/1.48      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_198,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_437,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_436]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_441,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_437,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1796,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_441]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3459,plain,
% 7.34/1.48      ( r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_1781,c_1796]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_789,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_790,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_789]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_794,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_790,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1782,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_794]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_5134,plain,
% 7.34/1.48      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | ~ r2_hidden(X0_54,X0_55)
% 7.34/1.48      | r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_3459,c_1782]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_5135,plain,
% 7.34/1.48      ( r1_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ r2_hidden(X0_54,X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_5134]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_6,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_873,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_874,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_873]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_878,plain,
% 7.34/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
% 7.34/1.48      | r4_lattice3(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_874,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_879,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | ~ r1_lattices(sK4,sK0(sK4,X0,X1),X0)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_878]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1778,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | ~ r1_lattices(sK4,sK0(sK4,X0_54,X0_55),X0_54)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_879]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_5156,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55)
% 7.34/1.48      | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_5135,c_1778]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_8,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_831,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_31]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_832,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_831]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_836,plain,
% 7.34/1.48      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | r4_lattice3(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_832,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_837,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_836]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1780,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 7.34/1.48      | m1_subset_1(sK0(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_837]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2496,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1780]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_11486,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_5156,c_1782,c_2496]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_19319,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55)
% 7.34/1.48      | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55),sK5)
% 7.34/1.48      | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_19297,c_11486]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_19321,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
% 7.34/1.48      | ~ r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),sK5)
% 7.34/1.48      | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_19319]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_7,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_852,plain,
% 7.34/1.48      ( r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_7,c_31]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_853,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r2_hidden(sK0(sK4,X0,X1),X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_852]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_857,plain,
% 7.34/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | r2_hidden(sK0(sK4,X0,X1),X1)
% 7.34/1.48      | r4_lattice3(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_853,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_858,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r2_hidden(sK0(sK4,X0,X1),X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_857]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1779,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_858]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2517,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | r2_hidden(sK0(sK4,k15_lattice3(sK4,X0_55),X1_55),X1_55)
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1779]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_6633,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
% 7.34/1.48      | r2_hidden(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),sK5)
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2517]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_6634,plain,
% 7.34/1.48      ( r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
% 7.34/1.48      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2496]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_6182,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1782]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1809,plain,
% 7.34/1.48      ( ~ r4_lattice3(X0_53,X0_54,X0_55)
% 7.34/1.48      | r4_lattice3(X0_53,X1_54,X0_55)
% 7.34/1.48      | X1_54 != X0_54 ),
% 7.34/1.48      theory(equality) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2614,plain,
% 7.34/1.48      ( r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | ~ r4_lattice3(sK4,k15_lattice3(sK4,X1_55),X0_55)
% 7.34/1.48      | X0_54 != k15_lattice3(sK4,X1_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1809]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2724,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | r4_lattice3(sK4,k15_lattice3(sK4,X2_55),X1_55)
% 7.34/1.48      | k15_lattice3(sK4,X2_55) != k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2614]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3413,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),sK5)
% 7.34/1.48      | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 7.34/1.48      | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2724]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_5082,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)),sK5)
% 7.34/1.48      | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 7.34/1.48      | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_3413]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_23,plain,
% 7.34/1.48      ( ~ v4_lattice3(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 7.34/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_451,plain,
% 7.34/1.48      ( ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_452,plain,
% 7.34/1.48      ( ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4)
% 7.34/1.48      | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_451]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_456,plain,
% 7.34/1.48      ( k15_lattice3(sK4,a_2_5_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_452,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1795,plain,
% 7.34/1.48      ( k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_456]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_4379,plain,
% 7.34/1.48      ( k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) = k15_lattice3(sK4,sK6) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1795]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2734,plain,
% 7.34/1.48      ( k15_lattice3(sK4,X0_55) = k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1802]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_4039,plain,
% 7.34/1.48      ( k15_lattice3(sK4,sK6) = k15_lattice3(sK4,sK6) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2734]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2603,plain,
% 7.34/1.48      ( X0_54 != X1_54
% 7.34/1.48      | X0_54 = k15_lattice3(sK4,X0_55)
% 7.34/1.48      | k15_lattice3(sK4,X0_55) != X1_54 ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1804]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2711,plain,
% 7.34/1.48      ( X0_54 != k15_lattice3(sK4,X0_55)
% 7.34/1.48      | X0_54 = k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) != k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2603]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2804,plain,
% 7.34/1.48      ( k15_lattice3(sK4,X0_55) != k15_lattice3(sK4,X0_55)
% 7.34/1.48      | k15_lattice3(sK4,X0_55) = k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55))
% 7.34/1.48      | k15_lattice3(sK4,a_2_5_lattice3(sK4,X0_55)) != k15_lattice3(sK4,X0_55) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2711]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_3510,plain,
% 7.34/1.48      ( k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6)) != k15_lattice3(sK4,sK6)
% 7.34/1.48      | k15_lattice3(sK4,sK6) = k15_lattice3(sK4,a_2_5_lattice3(sK4,sK6))
% 7.34/1.48      | k15_lattice3(sK4,sK6) != k15_lattice3(sK4,sK6) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2804]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_13,plain,
% 7.34/1.48      ( ~ r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 7.34/1.48      | ~ v4_lattice3(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_518,plain,
% 7.34/1.48      ( ~ r4_lattice3(X0,X1,X2)
% 7.34/1.48      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_519,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4)
% 7.34/1.48      | ~ v10_lattices(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_518]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_523,plain,
% 7.34/1.48      ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 7.34/1.48      | ~ r4_lattice3(sK4,X0,X1) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_519,c_31,c_30,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_524,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(renaming,[status(thm)],[c_523]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_895,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0,X1)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(backward_subsumption_resolution,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_794,c_524]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1777,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X0_55),X0_54)
% 7.34/1.48      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(subtyping,[status(esa)],[c_895]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2605,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,X1_55),k15_lattice3(sK4,X0_55))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1777]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2975,plain,
% 7.34/1.48      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 7.34/1.48      | r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_2605]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2796,plain,
% 7.34/1.48      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(instantiation,[status(thm)],[c_1782]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_24,negated_conjecture,
% 7.34/1.48      ( ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 7.34/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_0,plain,
% 7.34/1.48      ( ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0)
% 7.34/1.48      | v9_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_4,plain,
% 7.34/1.48      ( ~ r1_lattices(X0,X1,X2)
% 7.34/1.48      | r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ v6_lattices(X0)
% 7.34/1.48      | ~ v8_lattices(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v9_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_388,plain,
% 7.34/1.48      ( ~ r1_lattices(X0,X1,X2)
% 7.34/1.48      | r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ v6_lattices(X0)
% 7.34/1.48      | ~ v8_lattices(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_2,plain,
% 7.34/1.48      ( v6_lattices(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_1,plain,
% 7.34/1.48      ( v8_lattices(X0)
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_392,plain,
% 7.34/1.48      ( ~ r1_lattices(X0,X1,X2)
% 7.34/1.48      | r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | ~ v10_lattices(X0) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_388,c_2,c_1]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_731,plain,
% 7.34/1.48      ( ~ r1_lattices(X0,X1,X2)
% 7.34/1.48      | r3_lattices(X0,X1,X2)
% 7.34/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.34/1.48      | ~ l3_lattices(X0)
% 7.34/1.48      | v2_struct_0(X0)
% 7.34/1.48      | sK4 != X0 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_392,c_30]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_732,plain,
% 7.34/1.48      ( ~ r1_lattices(sK4,X0,X1)
% 7.34/1.48      | r3_lattices(sK4,X0,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.34/1.48      | ~ l3_lattices(sK4)
% 7.34/1.48      | v2_struct_0(sK4) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_731]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_736,plain,
% 7.34/1.48      ( ~ r1_lattices(sK4,X0,X1)
% 7.34/1.48      | r3_lattices(sK4,X0,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 7.34/1.48      inference(global_propositional_subsumption,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_732,c_31,c_28]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_969,plain,
% 7.34/1.48      ( ~ r1_lattices(sK4,X0,X1)
% 7.34/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.34/1.48      | k15_lattice3(sK4,sK6) != X1
% 7.34/1.48      | k15_lattice3(sK4,sK5) != X0
% 7.34/1.48      | sK4 != sK4 ),
% 7.34/1.48      inference(resolution_lifted,[status(thm)],[c_24,c_736]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_970,plain,
% 7.34/1.48      ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 7.34/1.48      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 7.34/1.48      inference(unflattening,[status(thm)],[c_969]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(c_978,plain,
% 7.34/1.48      ( ~ r1_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 7.34/1.48      inference(forward_subsumption_resolution,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_970,c_794,c_794]) ).
% 7.34/1.48  
% 7.34/1.48  cnf(contradiction,plain,
% 7.34/1.48      ( $false ),
% 7.34/1.48      inference(minisat,
% 7.34/1.48                [status(thm)],
% 7.34/1.48                [c_19321,c_6633,c_6634,c_6182,c_5082,c_4379,c_4039,
% 7.34/1.48                 c_3510,c_2975,c_2796,c_978]) ).
% 7.34/1.48  
% 7.34/1.48  
% 7.34/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.48  
% 7.34/1.48  ------                               Statistics
% 7.34/1.48  
% 7.34/1.48  ------ Selected
% 7.34/1.48  
% 7.34/1.48  total_time:                             0.602
% 7.34/1.48  
%------------------------------------------------------------------------------
