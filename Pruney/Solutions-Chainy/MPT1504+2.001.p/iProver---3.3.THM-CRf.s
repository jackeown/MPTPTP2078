%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:08 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  255 (1186 expanded)
%              Number of clauses        :  173 ( 294 expanded)
%              Number of leaves         :   23 ( 321 expanded)
%              Depth                    :   21
%              Number of atoms          : 1386 (6411 expanded)
%              Number of equality atoms :  198 (1017 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
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
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
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
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
     => k15_lattice3(X0,sK8) != k16_lattice3(X0,a_2_2_lattice3(X0,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK7,X1) != k16_lattice3(sK7,a_2_2_lattice3(sK7,X1))
      & l3_lattices(sK7)
      & v4_lattice3(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8))
    & l3_lattices(sK7)
    & v4_lattice3(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f55,f54])).

fof(f87,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK3(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK3(X0,X4),X4)
        & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X2))
        & r4_lattice3(X0,sK2(X0,X2),X1)
        & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK1(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK1(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK2(X0,X2))
                & r4_lattice3(X0,sK2(X0,X2),sK1(X0))
                & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK1(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK3(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK3(X0,X4),X4)
              & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f69,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK3(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f67,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK3(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK5(X0,X1,X2),X2)
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK5(X0,X1,X2),X2)
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
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

fof(f58,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f68,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK3(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1743,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_1744,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1743])).

cnf(c_31,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1748,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1744,c_31])).

cnf(c_1749,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1748])).

cnf(c_2819,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1749])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1647,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_1648,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK3(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1647])).

cnf(c_32,negated_conjecture,
    ( v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1652,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK3(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1648,c_32,c_31])).

cnf(c_2823,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_58)
    | r1_lattices(sK7,sK3(sK7,X0_58),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1652])).

cnf(c_4119,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
    | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
    | ~ m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_2819,c_2823])).

cnf(c_3330,plain,
    ( r4_lattice3(sK7,X0_55,X0_58) != iProver_top
    | r1_lattices(sK7,sK3(sK7,X0_58),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_3334,plain,
    ( r3_lattice3(sK7,X0_55,X0_56) = iProver_top
    | r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_4107,plain,
    ( r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58) != iProver_top
    | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top
    | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_3334])).

cnf(c_15,plain,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1617,plain,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_1618,plain,
    ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1617])).

cnf(c_1622,plain,
    ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1618,c_32,c_31])).

cnf(c_2825,plain,
    ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1622])).

cnf(c_2904,plain,
    ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1701,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_1702,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1701])).

cnf(c_1706,plain,
    ( m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1702,c_31])).

cnf(c_1707,plain,
    ( r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1706])).

cnf(c_2821,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK0(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1707])).

cnf(c_3532,plain,
    ( r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
    | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2821])).

cnf(c_3533,plain,
    ( r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top
    | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3532])).

cnf(c_4978,plain,
    ( r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58) != iProver_top
    | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4107,c_2904,c_3533])).

cnf(c_4980,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
    | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4978])).

cnf(c_5375,plain,
    ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
    | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4119,c_4980])).

cnf(c_2844,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_2843,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_4002,plain,
    ( X0_55 != X1_55
    | X1_55 = X0_55 ),
    inference(resolution,[status(thm)],[c_2844,c_2843])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK5(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1238,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK5(X0,X1,X2) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_1239,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | sK5(X0,sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1238])).

cnf(c_1243,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | sK5(X0,sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1239,c_34,c_32,c_31])).

cnf(c_2829,plain,
    ( ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
    | sK5(X0_55,sK7,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1243])).

cnf(c_4925,plain,
    ( ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
    | X0_55 = sK5(X0_55,sK7,X0_58) ),
    inference(resolution,[status(thm)],[c_4002,c_2829])).

cnf(c_2849,plain,
    ( ~ r4_lattice3(X0_54,X0_55,X0_58)
    | r4_lattice3(X0_54,X1_55,X0_58)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_5037,plain,
    ( r4_lattice3(X0_54,X0_55,X0_58)
    | ~ r4_lattice3(X0_54,sK5(X0_55,sK7,X1_58),X0_58)
    | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X1_58)) ),
    inference(resolution,[status(thm)],[c_4925,c_2849])).

cnf(c_22,plain,
    ( r4_lattice3(X0,sK5(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1067,plain,
    ( r4_lattice3(X0,sK5(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_1068,plain,
    ( r4_lattice3(sK7,sK5(X0,sK7,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1067])).

cnf(c_1072,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | r4_lattice3(sK7,sK5(X0,sK7,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1068,c_34,c_32,c_31])).

cnf(c_1073,plain,
    ( r4_lattice3(sK7,sK5(X0,sK7,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1)) ),
    inference(renaming,[status(thm)],[c_1072])).

cnf(c_2837,plain,
    ( r4_lattice3(sK7,sK5(X0_55,sK7,X0_58),X0_58)
    | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58)) ),
    inference(subtyping,[status(esa)],[c_1073])).

cnf(c_11655,plain,
    ( r4_lattice3(sK7,X0_55,X0_58)
    | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58)) ),
    inference(resolution,[status(thm)],[c_5037,c_2837])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1722,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_1723,plain,
    ( r3_lattice3(sK7,X0,X1)
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1722])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_31])).

cnf(c_1728,plain,
    ( r3_lattice3(sK7,X0,X1)
    | r2_hidden(sK0(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1727])).

cnf(c_2820,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | r2_hidden(sK0(sK7,X0_55,X0_56),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1728])).

cnf(c_12086,plain,
    ( r4_lattice3(sK7,sK0(sK7,X0_55,a_2_2_lattice3(sK7,X0_58)),X0_58)
    | r3_lattice3(sK7,X0_55,a_2_2_lattice3(sK7,X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_11655,c_2820])).

cnf(c_12220,plain,
    ( r3_lattice3(sK7,sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_5375,c_12086])).

cnf(c_12222,plain,
    ( r3_lattice3(sK7,sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_12220])).

cnf(c_2847,plain,
    ( ~ r3_lattice3(X0_54,X0_55,X0_56)
    | r3_lattice3(X0_54,X1_55,X0_56)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3667,plain,
    ( r3_lattice3(sK7,X0_55,X0_56)
    | ~ r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
    | X0_55 != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2847])).

cnf(c_4789,plain,
    ( r3_lattice3(sK7,k15_lattice3(sK7,X0_58),X0_56)
    | ~ r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
    | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_3667])).

cnf(c_10127,plain,
    ( r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
    | ~ r3_lattice3(sK7,sK3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
    | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_4789])).

cnf(c_10135,plain,
    ( r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ r3_lattice3(sK7,sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_10127])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1674,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_1675,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1674])).

cnf(c_1679,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1675,c_31])).

cnf(c_1680,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1679])).

cnf(c_2822,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,X0_55,X1_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1680])).

cnf(c_4177,plain,
    ( ~ r3_lattice3(sK7,X0_55,a_2_2_lattice3(sK7,X0_58))
    | r1_lattices(sK7,X0_55,k15_lattice3(sK7,X0_58))
    | ~ r2_hidden(k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2822])).

cnf(c_5907,plain,
    ( ~ r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),a_2_2_lattice3(sK7,X2_58))
    | r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),k15_lattice3(sK7,X2_58))
    | ~ r2_hidden(k15_lattice3(sK7,X2_58),a_2_2_lattice3(sK7,X2_58))
    | ~ m1_subset_1(sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,X2_58),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4177])).

cnf(c_5919,plain,
    ( ~ r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),a_2_2_lattice3(sK7,sK8))
    | r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),k15_lattice3(sK7,sK8))
    | ~ r2_hidden(k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ m1_subset_1(sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5907])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK4(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1172,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK4(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_1173,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1172])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1173,c_34,c_32,c_31])).

cnf(c_1178,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1177])).

cnf(c_2832,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_58)
    | r4_lattice3(sK7,sK4(sK7,X0_58,X0_55),X0_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1178])).

cnf(c_3321,plain,
    ( k15_lattice3(sK7,X0_58) = X0_55
    | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
    | r4_lattice3(sK7,sK4(sK7,X0_58,X0_55),X0_58) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2832])).

cnf(c_16,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1196,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_1197,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1196])).

cnf(c_1201,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1197,c_34,c_32,c_31])).

cnf(c_1202,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1201])).

cnf(c_2831,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_58)
    | ~ r1_lattices(sK7,X0_55,sK4(sK7,X0_58,X0_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1202])).

cnf(c_3322,plain,
    ( k15_lattice3(sK7,X0_58) = X0_55
    | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
    | r1_lattices(sK7,X0_55,sK4(sK7,X0_58,X0_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_4267,plain,
    ( k15_lattice3(sK7,X0_58) = sK3(sK7,X1_58)
    | r4_lattice3(sK7,sK4(sK7,X0_58,sK3(sK7,X1_58)),X1_58) != iProver_top
    | r4_lattice3(sK7,sK3(sK7,X1_58),X0_58) != iProver_top
    | m1_subset_1(sK4(sK7,X0_58,sK3(sK7,X1_58)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK3(sK7,X1_58),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_3322])).

cnf(c_3328,plain,
    ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_18,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1148,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_1149,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_1153,plain,
    ( m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_34,c_32,c_31])).

cnf(c_1154,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1153])).

cnf(c_2833,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0_58,X0_55),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_58) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1154])).

cnf(c_3320,plain,
    ( k15_lattice3(sK7,X0_58) = X0_55
    | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X0_58,X0_55),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2833])).

cnf(c_4992,plain,
    ( k15_lattice3(sK7,X0_58) = sK3(sK7,X1_58)
    | r4_lattice3(sK7,sK4(sK7,X0_58,sK3(sK7,X1_58)),X1_58) != iProver_top
    | r4_lattice3(sK7,sK3(sK7,X1_58),X0_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4267,c_3328,c_3320])).

cnf(c_4996,plain,
    ( k15_lattice3(sK7,X0_58) = sK3(sK7,X0_58)
    | r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) != iProver_top
    | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3321,c_4992])).

cnf(c_4998,plain,
    ( k15_lattice3(sK7,sK8) = sK3(sK7,sK8)
    | r4_lattice3(sK7,sK3(sK7,sK8),sK8) != iProver_top
    | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4996])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_402,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_406,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_2,c_1])).

cnf(c_905,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_406,c_33])).

cnf(c_906,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_910,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_34,c_31])).

cnf(c_911,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_910])).

cnf(c_25,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1043,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_1044,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_34,c_32,c_31])).

cnf(c_1049,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1048])).

cnf(c_1344,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | X0 != X3
    | sK6(sK7,X0,X1) != X2
    | k16_lattice3(sK7,X1) = X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_911,c_1049])).

cnf(c_1345,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1344])).

cnf(c_27,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_995,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_996,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_1000,plain,
    ( m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_34,c_32,c_31])).

cnf(c_1001,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1000])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_1001])).

cnf(c_1350,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1349])).

cnf(c_2827,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | ~ r1_lattices(sK7,sK6(sK7,X0_55,X0_56),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1350])).

cnf(c_4400,plain,
    ( ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
    | ~ r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),k15_lattice3(sK7,X0_58))
    | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_4417,plain,
    ( ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),k15_lattice3(sK7,sK8))
    | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4400])).

cnf(c_26,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1019,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k16_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_1020,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ r3_lattice3(sK7,X0,X1)
    | k16_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_34,c_32,c_31])).

cnf(c_1025,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k16_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1024])).

cnf(c_2838,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1025])).

cnf(c_4402,plain,
    ( r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),a_2_2_lattice3(sK7,X1_58))
    | ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
    | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_4409,plain,
    ( r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),a_2_2_lattice3(sK7,sK8))
    | ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4402])).

cnf(c_2839,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7))
    | k16_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_4403,plain,
    ( ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
    | m1_subset_1(sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_4405,plain,
    ( ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | m1_subset_1(sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
    | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4403])).

cnf(c_2848,plain,
    ( ~ r2_hidden(X0_55,X0_56)
    | r2_hidden(X1_55,X0_56)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3697,plain,
    ( r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
    | ~ r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | X0_55 != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_4076,plain,
    ( r2_hidden(k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | ~ r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_3697])).

cnf(c_4078,plain,
    ( r2_hidden(k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ r2_hidden(sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4076])).

cnf(c_2846,plain,
    ( ~ m1_subset_1(X0_55,X0_57)
    | m1_subset_1(X1_55,X0_57)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3610,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7))
    | X0_55 != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_3714,plain,
    ( m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_3716,plain,
    ( m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
    | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_3642,plain,
    ( k15_lattice3(sK7,sK8) = k15_lattice3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2843])).

cnf(c_3608,plain,
    ( k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) != X0_55
    | k15_lattice3(sK7,sK8) != X0_55
    | k15_lattice3(sK7,sK8) = k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_3641,plain,
    ( k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) != k15_lattice3(sK7,sK8)
    | k15_lattice3(sK7,sK8) = k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8))
    | k15_lattice3(sK7,sK8) != k15_lattice3(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_21,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1085,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_1086,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1085])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | ~ r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_34,c_32,c_31])).

cnf(c_1091,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1090])).

cnf(c_2836,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_58)
    | r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1091])).

cnf(c_3542,plain,
    ( ~ r4_lattice3(sK7,sK3(sK7,X0_58),X0_58)
    | r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
    | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_3544,plain,
    ( ~ r4_lattice3(sK7,sK3(sK7,sK8),sK8)
    | r2_hidden(sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
    | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_14,plain,
    ( r4_lattice3(X0,sK3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1632,plain,
    ( r4_lattice3(X0,sK3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_1633,plain,
    ( r4_lattice3(sK7,sK3(sK7,X0),X0)
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1632])).

cnf(c_1637,plain,
    ( r4_lattice3(sK7,sK3(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_32,c_31])).

cnf(c_2824,plain,
    ( r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) ),
    inference(subtyping,[status(esa)],[c_1637])).

cnf(c_2907,plain,
    ( r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_2909,plain,
    ( r4_lattice3(sK7,sK3(sK7,sK8),sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2907])).

cnf(c_2908,plain,
    ( r4_lattice3(sK7,sK3(sK7,sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_2906,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2904])).

cnf(c_2905,plain,
    ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_30,negated_conjecture,
    ( k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2841,negated_conjecture,
    ( k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12222,c_10135,c_5919,c_4998,c_4417,c_4409,c_4405,c_4078,c_3716,c_3642,c_3641,c_3544,c_2909,c_2908,c_2906,c_2905,c_2841])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.63/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.99  
% 3.63/0.99  ------  iProver source info
% 3.63/0.99  
% 3.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.99  git: non_committed_changes: false
% 3.63/0.99  git: last_make_outside_of_git: false
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  ------ Parsing...
% 3.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  ------ Proving...
% 3.63/0.99  ------ Problem Properties 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  clauses                                 23
% 3.63/0.99  conjectures                             1
% 3.63/0.99  EPR                                     0
% 3.63/0.99  Horn                                    17
% 3.63/0.99  unary                                   3
% 3.63/0.99  binary                                  5
% 3.63/0.99  lits                                    69
% 3.63/0.99  lits eq                                 9
% 3.63/0.99  fd_pure                                 0
% 3.63/0.99  fd_pseudo                               0
% 3.63/0.99  fd_cond                                 0
% 3.63/0.99  fd_pseudo_cond                          6
% 3.63/0.99  AC symbols                              0
% 3.63/0.99  
% 3.63/0.99  ------ Input Options Time Limit: Unbounded
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  Current options:
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS status Theorem for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  fof(f3,axiom,(
% 3.63/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f17,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f3])).
% 3.63/0.99  
% 3.63/0.99  fof(f18,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f17])).
% 3.63/0.99  
% 3.63/0.99  fof(f30,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f18])).
% 3.63/0.99  
% 3.63/0.99  fof(f31,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(rectify,[],[f30])).
% 3.63/0.99  
% 3.63/0.99  fof(f32,plain,(
% 3.63/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f33,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.63/0.99  
% 3.63/0.99  fof(f66,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f8,conjecture,(
% 3.63/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f9,negated_conjecture,(
% 3.63/0.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.63/0.99    inference(negated_conjecture,[],[f8])).
% 3.63/0.99  
% 3.63/0.99  fof(f27,plain,(
% 3.63/0.99    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f9])).
% 3.63/0.99  
% 3.63/0.99  fof(f28,plain,(
% 3.63/0.99    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f27])).
% 3.63/0.99  
% 3.63/0.99  fof(f55,plain,(
% 3.63/0.99    ( ! [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) => k15_lattice3(X0,sK8) != k16_lattice3(X0,a_2_2_lattice3(X0,sK8))) )),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f54,plain,(
% 3.63/0.99    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK7,X1) != k16_lattice3(sK7,a_2_2_lattice3(sK7,X1)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f56,plain,(
% 3.63/0.99    k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f55,f54])).
% 3.63/0.99  
% 3.63/0.99  fof(f87,plain,(
% 3.63/0.99    ~v2_struct_0(sK7)),
% 3.63/0.99    inference(cnf_transformation,[],[f56])).
% 3.63/0.99  
% 3.63/0.99  fof(f90,plain,(
% 3.63/0.99    l3_lattices(sK7)),
% 3.63/0.99    inference(cnf_transformation,[],[f56])).
% 3.63/0.99  
% 3.63/0.99  fof(f4,axiom,(
% 3.63/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f19,plain,(
% 3.63/0.99    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f4])).
% 3.63/0.99  
% 3.63/0.99  fof(f20,plain,(
% 3.63/0.99    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f19])).
% 3.63/0.99  
% 3.63/0.99  fof(f34,plain,(
% 3.63/0.99    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f20])).
% 3.63/0.99  
% 3.63/0.99  fof(f35,plain,(
% 3.63/0.99    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(rectify,[],[f34])).
% 3.63/0.99  
% 3.63/0.99  fof(f38,plain,(
% 3.63/0.99    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK3(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK3(X0,X4),X4) & m1_subset_1(sK3(X0,X4),u1_struct_0(X0))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f37,plain,(
% 3.63/0.99    ( ! [X1] : (! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X2)) & r4_lattice3(X0,sK2(X0,X2),X1) & m1_subset_1(sK2(X0,X2),u1_struct_0(X0))))) )),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f36,plain,(
% 3.63/0.99    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK1(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK1(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f39,plain,(
% 3.63/0.99    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK2(X0,X2)) & r4_lattice3(X0,sK2(X0,X2),sK1(X0)) & m1_subset_1(sK2(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK1(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK3(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK3(X0,X4),X4) & m1_subset_1(sK3(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 3.63/0.99  
% 3.63/0.99  fof(f69,plain,(
% 3.63/0.99    ( ! [X6,X4,X0] : (r1_lattices(X0,sK3(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f39])).
% 3.63/0.99  
% 3.63/0.99  fof(f89,plain,(
% 3.63/0.99    v4_lattice3(sK7)),
% 3.63/0.99    inference(cnf_transformation,[],[f56])).
% 3.63/0.99  
% 3.63/0.99  fof(f67,plain,(
% 3.63/0.99    ( ! [X4,X0] : (m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f39])).
% 3.63/0.99  
% 3.63/0.99  fof(f64,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f6,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f23,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.63/0.99    inference(ennf_transformation,[],[f6])).
% 3.63/0.99  
% 3.63/0.99  fof(f24,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.63/0.99    inference(flattening,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f45,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.63/0.99    inference(nnf_transformation,[],[f24])).
% 3.63/0.99  
% 3.63/0.99  fof(f46,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.63/0.99    inference(rectify,[],[f45])).
% 3.63/0.99  
% 3.63/0.99  fof(f47,plain,(
% 3.63/0.99    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f48,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 3.63/0.99  
% 3.63/0.99  fof(f79,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (sK5(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f48])).
% 3.63/0.99  
% 3.63/0.99  fof(f88,plain,(
% 3.63/0.99    v10_lattices(sK7)),
% 3.63/0.99    inference(cnf_transformation,[],[f56])).
% 3.63/0.99  
% 3.63/0.99  fof(f80,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK5(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f48])).
% 3.63/0.99  
% 3.63/0.99  fof(f65,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f63,plain,(
% 3.63/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f33])).
% 3.63/0.99  
% 3.63/0.99  fof(f5,axiom,(
% 3.63/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f21,plain,(
% 3.63/0.99    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f5])).
% 3.63/0.99  
% 3.63/0.99  fof(f22,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f21])).
% 3.63/0.99  
% 3.63/0.99  fof(f40,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f22])).
% 3.63/0.99  
% 3.63/0.99  fof(f41,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f40])).
% 3.63/0.99  
% 3.63/0.99  fof(f42,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(rectify,[],[f41])).
% 3.63/0.99  
% 3.63/0.99  fof(f43,plain,(
% 3.63/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f44,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 3.63/0.99  
% 3.63/0.99  fof(f76,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK4(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f44])).
% 3.63/0.99  
% 3.63/0.99  fof(f77,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f44])).
% 3.63/0.99  
% 3.63/0.99  fof(f75,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f44])).
% 3.63/0.99  
% 3.63/0.99  fof(f1,axiom,(
% 3.63/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f10,plain,(
% 3.63/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.63/0.99    inference(pure_predicate_removal,[],[f1])).
% 3.63/0.99  
% 3.63/0.99  fof(f11,plain,(
% 3.63/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.63/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.63/0.99  
% 3.63/0.99  fof(f12,plain,(
% 3.63/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.63/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.63/0.99  
% 3.63/0.99  fof(f13,plain,(
% 3.63/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.63/0.99    inference(ennf_transformation,[],[f12])).
% 3.63/0.99  
% 3.63/0.99  fof(f14,plain,(
% 3.63/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.63/0.99    inference(flattening,[],[f13])).
% 3.63/0.99  
% 3.63/0.99  fof(f60,plain,(
% 3.63/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f2,axiom,(
% 3.63/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f15,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f2])).
% 3.63/0.99  
% 3.63/0.99  fof(f16,plain,(
% 3.63/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f15])).
% 3.63/0.99  
% 3.63/0.99  fof(f29,plain,(
% 3.63/0.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f16])).
% 3.63/0.99  
% 3.63/0.99  fof(f62,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f29])).
% 3.63/0.99  
% 3.63/0.99  fof(f58,plain,(
% 3.63/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f59,plain,(
% 3.63/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f7,axiom,(
% 3.63/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.63/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f25,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.63/0.99    inference(ennf_transformation,[],[f7])).
% 3.63/0.99  
% 3.63/0.99  fof(f26,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f25])).
% 3.63/0.99  
% 3.63/0.99  fof(f49,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f26])).
% 3.63/0.99  
% 3.63/0.99  fof(f50,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(flattening,[],[f49])).
% 3.63/0.99  
% 3.63/0.99  fof(f51,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(rectify,[],[f50])).
% 3.63/0.99  
% 3.63/0.99  fof(f52,plain,(
% 3.63/0.99    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f53,plain,(
% 3.63/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 3.63/0.99  
% 3.63/0.99  fof(f86,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK6(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f53])).
% 3.63/0.99  
% 3.63/0.99  fof(f84,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f53])).
% 3.63/0.99  
% 3.63/0.99  fof(f85,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK6(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f53])).
% 3.63/0.99  
% 3.63/0.99  fof(f81,plain,(
% 3.63/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f48])).
% 3.63/0.99  
% 3.63/0.99  fof(f94,plain,(
% 3.63/0.99    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.63/0.99    inference(equality_resolution,[],[f81])).
% 3.63/0.99  
% 3.63/0.99  fof(f68,plain,(
% 3.63/0.99    ( ! [X4,X0] : (r4_lattice3(X0,sK3(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f39])).
% 3.63/0.99  
% 3.63/0.99  fof(f91,plain,(
% 3.63/0.99    k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8))),
% 3.63/0.99    inference(cnf_transformation,[],[f56])).
% 3.63/0.99  
% 3.63/0.99  cnf(c_6,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_34,negated_conjecture,
% 3.63/0.99      ( ~ v2_struct_0(sK7) ),
% 3.63/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1743,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1744,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1743]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_31,negated_conjecture,
% 3.63/0.99      ( l3_lattices(sK7) ),
% 3.63/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1748,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 3.63/0.99      | r3_lattice3(sK7,X0,X1) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1744,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1749,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | ~ r1_lattices(sK7,X0,sK0(sK7,X0,X1))
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1748]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2819,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0_55,X0_56)
% 3.63/0.99      | ~ r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56))
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1749]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | r1_lattices(X0,sK3(X0,X2),X1)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1647,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | r1_lattices(X0,sK3(X0,X2),X1)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1648,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/0.99      | r1_lattices(sK7,sK3(sK7,X1),X0)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ v4_lattice3(sK7)
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1647]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_32,negated_conjecture,
% 3.63/0.99      ( v4_lattice3(sK7) ),
% 3.63/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1652,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/0.99      | r1_lattices(sK7,sK3(sK7,X1),X0)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1648,c_32,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2823,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0_55,X0_58)
% 3.63/0.99      | r1_lattices(sK7,sK3(sK7,X0_58),X0_55)
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1652]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4119,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
% 3.63/0.99      | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
% 3.63/0.99      | ~ m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_2819,c_2823]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3330,plain,
% 3.63/0.99      ( r4_lattice3(sK7,X0_55,X0_58) != iProver_top
% 3.63/0.99      | r1_lattices(sK7,sK3(sK7,X0_58),X0_55) = iProver_top
% 3.63/0.99      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2823]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3334,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0_55,X0_56) = iProver_top
% 3.63/0.99      | r1_lattices(sK7,X0_55,sK0(sK7,X0_55,X0_56)) != iProver_top
% 3.63/0.99      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4107,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58) != iProver_top
% 3.63/0.99      | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top
% 3.63/0.99      | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7)) != iProver_top
% 3.63/0.99      | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3330,c_3334]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_15,plain,
% 3.63/0.99      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1617,plain,
% 3.63/0.99      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1618,plain,
% 3.63/0.99      ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7))
% 3.63/0.99      | ~ v4_lattice3(sK7)
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1617]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1622,plain,
% 3.63/0.99      ( m1_subset_1(sK3(sK7,X0),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1618,c_32,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2825,plain,
% 3.63/0.99      ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1622]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2904,plain,
% 3.63/0.99      ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_8,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1701,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1702,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1701]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1706,plain,
% 3.63/0.99      ( m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | r3_lattice3(sK7,X0,X1) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1702,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1707,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1706]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2821,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0_55,X0_56)
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/0.99      | m1_subset_1(sK0(sK7,X0_55,X0_56),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1707]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3532,plain,
% 3.63/0.99      ( r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
% 3.63/0.99      | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_2821]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3533,plain,
% 3.63/0.99      ( r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top
% 3.63/0.99      | m1_subset_1(sK0(sK7,sK3(sK7,X0_58),X0_56),u1_struct_0(sK7)) = iProver_top
% 3.63/0.99      | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_3532]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4978,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58) != iProver_top
% 3.63/0.99      | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) = iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_4107,c_2904,c_3533]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4980,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
% 3.63/0.99      | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) ),
% 3.63/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4978]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5375,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,sK0(sK7,sK3(sK7,X0_58),X0_56),X0_58)
% 3.63/0.99      | r3_lattice3(sK7,sK3(sK7,X0_58),X0_56) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_4119,c_4980]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2844,plain,
% 3.63/0.99      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 3.63/0.99      theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2843,plain,( X0_55 = X0_55 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4002,plain,
% 3.63/0.99      ( X0_55 != X1_55 | X1_55 = X0_55 ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_2844,c_2843]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_23,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.63/0.99      | ~ v4_lattice3(X1)
% 3.63/0.99      | ~ l3_lattices(X1)
% 3.63/0.99      | v2_struct_0(X1)
% 3.63/0.99      | ~ v10_lattices(X1)
% 3.63/0.99      | sK5(X0,X1,X2) = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_33,negated_conjecture,
% 3.63/0.99      ( v10_lattices(sK7) ),
% 3.63/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1238,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.63/0.99      | ~ v4_lattice3(X1)
% 3.63/0.99      | ~ l3_lattices(X1)
% 3.63/0.99      | v2_struct_0(X1)
% 3.63/0.99      | sK5(X0,X1,X2) = X0
% 3.63/0.99      | sK7 != X1 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1239,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/0.99      | ~ v4_lattice3(sK7)
% 3.63/0.99      | ~ l3_lattices(sK7)
% 3.63/0.99      | v2_struct_0(sK7)
% 3.63/0.99      | sK5(X0,sK7,X1) = X0 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1238]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1243,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1)) | sK5(X0,sK7,X1) = X0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1239,c_34,c_32,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2829,plain,
% 3.63/0.99      ( ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | sK5(X0_55,sK7,X0_58) = X0_55 ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1243]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4925,plain,
% 3.63/0.99      ( ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | X0_55 = sK5(X0_55,sK7,X0_58) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_4002,c_2829]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2849,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0_54,X0_55,X0_58)
% 3.63/0.99      | r4_lattice3(X0_54,X1_55,X0_58)
% 3.63/0.99      | X1_55 != X0_55 ),
% 3.63/0.99      theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5037,plain,
% 3.63/0.99      ( r4_lattice3(X0_54,X0_55,X0_58)
% 3.63/0.99      | ~ r4_lattice3(X0_54,sK5(X0_55,sK7,X1_58),X0_58)
% 3.63/0.99      | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X1_58)) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_4925,c_2849]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_22,plain,
% 3.63/0.99      ( r4_lattice3(X0,sK5(X1,X0,X2),X2)
% 3.63/0.99      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0)
% 3.63/0.99      | ~ v10_lattices(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1067,plain,
% 3.63/0.99      ( r4_lattice3(X0,sK5(X1,X0,X2),X2)
% 3.63/0.99      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1068,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK5(X0,sK7,X1),X1)
% 3.63/0.99      | ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/0.99      | ~ v4_lattice3(sK7)
% 3.63/0.99      | ~ l3_lattices(sK7)
% 3.63/0.99      | v2_struct_0(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1067]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1072,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/0.99      | r4_lattice3(sK7,sK5(X0,sK7,X1),X1) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1068,c_34,c_32,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1073,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK5(X0,sK7,X1),X1)
% 3.63/0.99      | ~ r2_hidden(X0,a_2_2_lattice3(sK7,X1)) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1072]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2837,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK5(X0_55,sK7,X0_58),X0_58)
% 3.63/0.99      | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1073]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_11655,plain,
% 3.63/0.99      ( r4_lattice3(sK7,X0_55,X0_58)
% 3.63/0.99      | ~ r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58)) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_5037,c_2837]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_7,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1722,plain,
% 3.63/0.99      ( r3_lattice3(X0,X1,X2)
% 3.63/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1723,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | r2_hidden(sK0(sK7,X0,X1),X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1722]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1727,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | r2_hidden(sK0(sK7,X0,X1),X1)
% 3.63/0.99      | r3_lattice3(sK7,X0,X1) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1723,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1728,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | r2_hidden(sK0(sK7,X0,X1),X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1727]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2820,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0_55,X0_56)
% 3.63/0.99      | r2_hidden(sK0(sK7,X0_55,X0_56),X0_56)
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1728]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12086,plain,
% 3.63/0.99      ( r4_lattice3(sK7,sK0(sK7,X0_55,a_2_2_lattice3(sK7,X0_58)),X0_58)
% 3.63/0.99      | r3_lattice3(sK7,X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_11655,c_2820]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12220,plain,
% 3.63/0.99      ( r3_lattice3(sK7,sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(resolution,[status(thm)],[c_5375,c_12086]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12222,plain,
% 3.63/0.99      ( r3_lattice3(sK7,sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/0.99      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_12220]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2847,plain,
% 3.63/0.99      ( ~ r3_lattice3(X0_54,X0_55,X0_56)
% 3.63/0.99      | r3_lattice3(X0_54,X1_55,X0_56)
% 3.63/0.99      | X1_55 != X0_55 ),
% 3.63/0.99      theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3667,plain,
% 3.63/0.99      ( r3_lattice3(sK7,X0_55,X0_56)
% 3.63/0.99      | ~ r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
% 3.63/0.99      | X0_55 != sK3(sK7,X0_58) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_2847]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4789,plain,
% 3.63/0.99      ( r3_lattice3(sK7,k15_lattice3(sK7,X0_58),X0_56)
% 3.63/0.99      | ~ r3_lattice3(sK7,sK3(sK7,X0_58),X0_56)
% 3.63/0.99      | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_3667]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_10127,plain,
% 3.63/0.99      ( r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
% 3.63/0.99      | ~ r3_lattice3(sK7,sK3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
% 3.63/0.99      | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_4789]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_10135,plain,
% 3.63/0.99      ( r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/0.99      | ~ r3_lattice3(sK7,sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/0.99      | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_10127]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_9,plain,
% 3.63/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/0.99      | r1_lattices(X0,X1,X3)
% 3.63/0.99      | ~ r2_hidden(X3,X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1674,plain,
% 3.63/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/0.99      | r1_lattices(X0,X1,X3)
% 3.63/0.99      | ~ r2_hidden(X3,X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1675,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | r1_lattices(sK7,X0,X2)
% 3.63/0.99      | ~ r2_hidden(X2,X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.63/0.99      | ~ l3_lattices(sK7) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1674]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1679,plain,
% 3.63/0.99      ( ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ r2_hidden(X2,X1)
% 3.63/0.99      | r1_lattices(sK7,X0,X2)
% 3.63/0.99      | ~ r3_lattice3(sK7,X0,X1) ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1675,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1680,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/0.99      | r1_lattices(sK7,X0,X2)
% 3.63/0.99      | ~ r2_hidden(X2,X1)
% 3.63/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1679]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2822,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 3.63/0.99      | r1_lattices(sK7,X0_55,X1_55)
% 3.63/0.99      | ~ r2_hidden(X1_55,X0_56)
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1680]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4177,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | r1_lattices(sK7,X0_55,k15_lattice3(sK7,X0_58))
% 3.63/0.99      | ~ r2_hidden(k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_2822]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5907,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),a_2_2_lattice3(sK7,X2_58))
% 3.63/0.99      | r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),k15_lattice3(sK7,X2_58))
% 3.63/0.99      | ~ r2_hidden(k15_lattice3(sK7,X2_58),a_2_2_lattice3(sK7,X2_58))
% 3.63/0.99      | ~ m1_subset_1(sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(k15_lattice3(sK7,X2_58),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_4177]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5919,plain,
% 3.63/0.99      ( ~ r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),a_2_2_lattice3(sK7,sK8))
% 3.63/0.99      | r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),k15_lattice3(sK7,sK8))
% 3.63/0.99      | ~ r2_hidden(k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/0.99      | ~ m1_subset_1(sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),u1_struct_0(sK7))
% 3.63/0.99      | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7)) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_5907]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | r4_lattice3(X0,sK4(X0,X2,X1),X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0)
% 3.63/0.99      | ~ v10_lattices(X0)
% 3.63/0.99      | k15_lattice3(X0,X2) = X1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1172,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | r4_lattice3(X0,sK4(X0,X2,X1),X2)
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0)
% 3.63/0.99      | k15_lattice3(X0,X2) = X1
% 3.63/0.99      | sK7 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1173,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/0.99      | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | ~ v4_lattice3(sK7)
% 3.63/0.99      | ~ l3_lattices(sK7)
% 3.63/0.99      | v2_struct_0(sK7)
% 3.63/0.99      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_1172]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1177,plain,
% 3.63/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
% 3.63/0.99      | ~ r4_lattice3(sK7,X0,X1)
% 3.63/0.99      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1173,c_34,c_32,c_31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1178,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/0.99      | r4_lattice3(sK7,sK4(sK7,X1,X0),X1)
% 3.63/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/0.99      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_1177]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2832,plain,
% 3.63/0.99      ( ~ r4_lattice3(sK7,X0_55,X0_58)
% 3.63/0.99      | r4_lattice3(sK7,sK4(sK7,X0_58,X0_55),X0_58)
% 3.63/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/0.99      | k15_lattice3(sK7,X0_58) = X0_55 ),
% 3.63/0.99      inference(subtyping,[status(esa)],[c_1178]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3321,plain,
% 3.63/0.99      ( k15_lattice3(sK7,X0_58) = X0_55
% 3.63/0.99      | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
% 3.63/0.99      | r4_lattice3(sK7,sK4(sK7,X0_58,X0_55),X0_58) = iProver_top
% 3.63/0.99      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2832]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_16,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
% 3.63/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/0.99      | ~ v4_lattice3(X0)
% 3.63/0.99      | ~ l3_lattices(X0)
% 3.63/0.99      | v2_struct_0(X0)
% 3.63/0.99      | ~ v10_lattices(X0)
% 3.63/0.99      | k15_lattice3(X0,X2) = X1 ),
% 3.63/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1196,plain,
% 3.63/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/0.99      | ~ r1_lattices(X0,X1,sK4(X0,X2,X1))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | k15_lattice3(X0,X2) = X1
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1197,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7)
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1196]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1201,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 3.63/1.00      | ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1197,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1202,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r1_lattices(sK7,X0,sK4(sK7,X1,X0))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1201]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2831,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_58)
% 3.63/1.00      | ~ r1_lattices(sK7,X0_55,sK4(sK7,X0_58,X0_55))
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,X0_58) = X0_55 ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1202]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3322,plain,
% 3.63/1.00      ( k15_lattice3(sK7,X0_58) = X0_55
% 3.63/1.00      | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
% 3.63/1.00      | r1_lattices(sK7,X0_55,sK4(sK7,X0_58,X0_55)) != iProver_top
% 3.63/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4267,plain,
% 3.63/1.00      ( k15_lattice3(sK7,X0_58) = sK3(sK7,X1_58)
% 3.63/1.00      | r4_lattice3(sK7,sK4(sK7,X0_58,sK3(sK7,X1_58)),X1_58) != iProver_top
% 3.63/1.00      | r4_lattice3(sK7,sK3(sK7,X1_58),X0_58) != iProver_top
% 3.63/1.00      | m1_subset_1(sK4(sK7,X0_58,sK3(sK7,X1_58)),u1_struct_0(sK7)) != iProver_top
% 3.63/1.00      | m1_subset_1(sK3(sK7,X1_58),u1_struct_0(sK7)) != iProver_top ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_3330,c_3322]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3328,plain,
% 3.63/1.00      ( m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_18,plain,
% 3.63/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0)
% 3.63/1.00      | k15_lattice3(X0,X2) = X1 ),
% 3.63/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1148,plain,
% 3.63/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | m1_subset_1(sK4(X0,X2,X1),u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | k15_lattice3(X0,X2) = X1
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1149,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7)
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1148]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1153,plain,
% 3.63/1.00      ( m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1149,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1154,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1153]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2833,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_58)
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK4(sK7,X0_58,X0_55),u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,X0_58) = X0_55 ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1154]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3320,plain,
% 3.63/1.00      ( k15_lattice3(sK7,X0_58) = X0_55
% 3.63/1.00      | r4_lattice3(sK7,X0_55,X0_58) != iProver_top
% 3.63/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top
% 3.63/1.00      | m1_subset_1(sK4(sK7,X0_58,X0_55),u1_struct_0(sK7)) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2833]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4992,plain,
% 3.63/1.00      ( k15_lattice3(sK7,X0_58) = sK3(sK7,X1_58)
% 3.63/1.00      | r4_lattice3(sK7,sK4(sK7,X0_58,sK3(sK7,X1_58)),X1_58) != iProver_top
% 3.63/1.00      | r4_lattice3(sK7,sK3(sK7,X1_58),X0_58) != iProver_top ),
% 3.63/1.00      inference(forward_subsumption_resolution,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_4267,c_3328,c_3320]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4996,plain,
% 3.63/1.00      ( k15_lattice3(sK7,X0_58) = sK3(sK7,X0_58)
% 3.63/1.00      | r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) != iProver_top
% 3.63/1.00      | m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) != iProver_top ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_3321,c_4992]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4998,plain,
% 3.63/1.00      ( k15_lattice3(sK7,sK8) = sK3(sK7,sK8)
% 3.63/1.00      | r4_lattice3(sK7,sK3(sK7,sK8),sK8) != iProver_top
% 3.63/1.00      | m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) != iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_4996]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_0,plain,
% 3.63/1.00      ( ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0)
% 3.63/1.00      | v9_lattices(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4,plain,
% 3.63/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.63/1.00      | r3_lattices(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v6_lattices(X0)
% 3.63/1.00      | ~ v8_lattices(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v9_lattices(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_402,plain,
% 3.63/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.63/1.00      | r3_lattices(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v6_lattices(X0)
% 3.63/1.00      | ~ v8_lattices(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0) ),
% 3.63/1.00      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2,plain,
% 3.63/1.00      ( v6_lattices(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1,plain,
% 3.63/1.00      ( v8_lattices(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_406,plain,
% 3.63/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.63/1.00      | r3_lattices(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_402,c_2,c_1]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_905,plain,
% 3.63/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.63/1.00      | r3_lattices(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_406,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_906,plain,
% 3.63/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 3.63/1.00      | r3_lattices(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_905]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_910,plain,
% 3.63/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 3.63/1.00      | r3_lattices(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_906,c_34,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_911,plain,
% 3.63/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 3.63/1.00      | r3_lattices(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_910]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_25,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1 ),
% 3.63/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1043,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1044,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1043]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1048,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1044,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1049,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r3_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1048]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1344,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r1_lattices(sK7,X2,X3)
% 3.63/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 3.63/1.00      | X0 != X3
% 3.63/1.00      | sK6(sK7,X0,X1) != X2
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0
% 3.63/1.00      | sK7 != sK7 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_911,c_1049]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1345,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1344]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_27,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1 ),
% 3.63/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_995,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_996,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_995]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1000,plain,
% 3.63/1.00      ( m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_996,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1001,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK6(sK7,X0,X1),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1000]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1349,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1345,c_1001]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1350,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,X0,X1),X0)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1349]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2827,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,X0_55,X0_56),X0_55)
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1350]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4400,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),k15_lattice3(sK7,X0_58))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2827]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4417,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | ~ r1_lattices(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),k15_lattice3(sK7,sK8))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_4400]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_26,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1 ),
% 3.63/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1019,plain,
% 3.63/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.63/1.00      | r3_lattice3(X0,sK6(X0,X1,X2),X2)
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | k16_lattice3(X0,X2) = X1
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1020,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1019]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1024,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 3.63/1.00      | ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1020,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1025,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 3.63/1.00      | r3_lattice3(sK7,sK6(sK7,X0,X1),X1)
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X1) = X0 ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1024]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2838,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 3.63/1.00      | r3_lattice3(sK7,sK6(sK7,X0_55,X0_56),X0_56)
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1025]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4402,plain,
% 3.63/1.00      ( r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),a_2_2_lattice3(sK7,X1_58))
% 3.63/1.00      | ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2838]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4409,plain,
% 3.63/1.00      ( r3_lattice3(sK7,sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_4402]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2839,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | m1_subset_1(sK6(sK7,X0_55,X0_56),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,X0_56) = X0_55 ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1001]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4403,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58))
% 3.63/1.00      | m1_subset_1(sK6(sK7,k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X1_58)),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,X1_58)) = k15_lattice3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2839]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4405,plain,
% 3.63/1.00      ( ~ r3_lattice3(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | m1_subset_1(sK6(sK7,k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8)),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
% 3.63/1.00      | k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) = k15_lattice3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_4403]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2848,plain,
% 3.63/1.00      ( ~ r2_hidden(X0_55,X0_56)
% 3.63/1.00      | r2_hidden(X1_55,X0_56)
% 3.63/1.00      | X1_55 != X0_55 ),
% 3.63/1.00      theory(equality) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3697,plain,
% 3.63/1.00      ( r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | ~ r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | X0_55 != sK3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2848]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4076,plain,
% 3.63/1.00      ( r2_hidden(k15_lattice3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | ~ r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_3697]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4078,plain,
% 3.63/1.00      ( r2_hidden(k15_lattice3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | ~ r2_hidden(sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_4076]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2846,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0_55,X0_57)
% 3.63/1.00      | m1_subset_1(X1_55,X0_57)
% 3.63/1.00      | X1_55 != X0_55 ),
% 3.63/1.00      theory(equality) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3610,plain,
% 3.63/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | X0_55 != sK3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2846]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3714,plain,
% 3.63/1.00      ( m1_subset_1(k15_lattice3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,X0_58) != sK3(sK7,X0_58) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_3610]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3716,plain,
% 3.63/1.00      ( m1_subset_1(k15_lattice3(sK7,sK8),u1_struct_0(sK7))
% 3.63/1.00      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7))
% 3.63/1.00      | k15_lattice3(sK7,sK8) != sK3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_3714]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3642,plain,
% 3.63/1.00      ( k15_lattice3(sK7,sK8) = k15_lattice3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2843]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3608,plain,
% 3.63/1.00      ( k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) != X0_55
% 3.63/1.00      | k15_lattice3(sK7,sK8) != X0_55
% 3.63/1.00      | k15_lattice3(sK7,sK8) = k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2844]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3641,plain,
% 3.63/1.00      ( k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) != k15_lattice3(sK7,sK8)
% 3.63/1.00      | k15_lattice3(sK7,sK8) = k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | k15_lattice3(sK7,sK8) != k15_lattice3(sK7,sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_3608]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_21,plain,
% 3.63/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | ~ v10_lattices(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1085,plain,
% 3.63/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.63/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.63/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0)
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1086,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7)
% 3.63/1.00      | v2_struct_0(sK7) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1085]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1090,plain,
% 3.63/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.63/1.00      | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/1.00      | ~ r4_lattice3(sK7,X0,X1) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1086,c_34,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1091,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 3.63/1.00      | r2_hidden(X0,a_2_2_lattice3(sK7,X1))
% 3.63/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.63/1.00      inference(renaming,[status(thm)],[c_1090]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2836,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_58)
% 3.63/1.00      | r2_hidden(X0_55,a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1091]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3542,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,sK3(sK7,X0_58),X0_58)
% 3.63/1.00      | r2_hidden(sK3(sK7,X0_58),a_2_2_lattice3(sK7,X0_58))
% 3.63/1.00      | ~ m1_subset_1(sK3(sK7,X0_58),u1_struct_0(sK7)) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2836]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3544,plain,
% 3.63/1.00      ( ~ r4_lattice3(sK7,sK3(sK7,sK8),sK8)
% 3.63/1.00      | r2_hidden(sK3(sK7,sK8),a_2_2_lattice3(sK7,sK8))
% 3.63/1.00      | ~ m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_3542]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_14,plain,
% 3.63/1.00      ( r4_lattice3(X0,sK3(X0,X1),X1)
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | v2_struct_0(X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1632,plain,
% 3.63/1.00      ( r4_lattice3(X0,sK3(X0,X1),X1)
% 3.63/1.00      | ~ v4_lattice3(X0)
% 3.63/1.00      | ~ l3_lattices(X0)
% 3.63/1.00      | sK7 != X0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1633,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,X0),X0)
% 3.63/1.00      | ~ v4_lattice3(sK7)
% 3.63/1.00      | ~ l3_lattices(sK7) ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_1632]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1637,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,X0),X0) ),
% 3.63/1.00      inference(global_propositional_subsumption,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_1633,c_32,c_31]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2824,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_1637]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2907,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,X0_58),X0_58) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_2824]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2909,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,sK8),sK8) = iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2907]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2908,plain,
% 3.63/1.00      ( r4_lattice3(sK7,sK3(sK7,sK8),sK8) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2824]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2906,plain,
% 3.63/1.00      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) = iProver_top ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2904]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2905,plain,
% 3.63/1.00      ( m1_subset_1(sK3(sK7,sK8),u1_struct_0(sK7)) ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2825]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_30,negated_conjecture,
% 3.63/1.00      ( k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
% 3.63/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2841,negated_conjecture,
% 3.63/1.00      ( k15_lattice3(sK7,sK8) != k16_lattice3(sK7,a_2_2_lattice3(sK7,sK8)) ),
% 3.63/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(contradiction,plain,
% 3.63/1.00      ( $false ),
% 3.63/1.00      inference(minisat,
% 3.63/1.00                [status(thm)],
% 3.63/1.00                [c_12222,c_10135,c_5919,c_4998,c_4417,c_4409,c_4405,
% 3.63/1.00                 c_4078,c_3716,c_3642,c_3641,c_3544,c_2909,c_2908,c_2906,
% 3.63/1.00                 c_2905,c_2841]) ).
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  ------                               Statistics
% 3.63/1.00  
% 3.63/1.00  ------ Selected
% 3.63/1.00  
% 3.63/1.00  total_time:                             0.429
% 3.63/1.00  
%------------------------------------------------------------------------------
