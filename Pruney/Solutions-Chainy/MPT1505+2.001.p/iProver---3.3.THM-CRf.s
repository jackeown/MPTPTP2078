%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:09 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 752 expanded)
%              Number of clauses        :  109 ( 166 expanded)
%              Number of leaves         :   20 ( 229 expanded)
%              Depth                    :   17
%              Number of atoms          : 1143 (5442 expanded)
%              Number of equality atoms :  100 ( 135 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK4(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK4(X0,X4),X4)
        & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK3(X0,X2))
        & r4_lattice3(X0,sK3(X0,X2),X1)
        & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
              & r4_lattice3(X0,X3,sK2(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK2(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK3(X0,X2))
                & r4_lattice3(X0,sK3(X0,X2),sK2(X0))
                & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK2(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK4(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK4(X0,X4),X4)
              & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).

fof(f77,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK4(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r2_hidden(X1,X2)
               => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
            | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
          & r2_hidden(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK9),X1)
          | ~ r3_lattices(X0,X1,k15_lattice3(X0,sK9)) )
        & r2_hidden(X1,sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),sK8)
              | ~ r3_lattices(X0,sK8,k15_lattice3(X0,X2)) )
            & r2_hidden(sK8,X2) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK7,k16_lattice3(sK7,X2),X1)
                | ~ r3_lattices(sK7,X1,k15_lattice3(sK7,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK7)) )
      & l3_lattices(sK7)
      & v4_lattice3(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
      | ~ r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9)) )
    & r2_hidden(sK8,sK9)
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l3_lattices(sK7)
    & v4_lattice3(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f59,f58,f57])).

fof(f92,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK5(X0,X1,X2))
        & r4_lattice3(X0,sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK5(X0,X1,X2))
                & r4_lattice3(X0,sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK5(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK5(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),X2)
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f11,plain,(
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

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK4(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK4(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f98,plain,
    ( ~ r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | ~ r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9)) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    r2_hidden(sK8,sK9) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK4(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1107,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,sK4(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_1108,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK4(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1107])).

cnf(c_35,negated_conjecture,
    ( v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_34,negated_conjecture,
    ( l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1112,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,sK4(sK7,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_35,c_34])).

cnf(c_2787,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,sK4(sK7,X0_56),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1112])).

cnf(c_3347,plain,
    ( r4_lattice3(sK7,X0_55,X0_56) != iProver_top
    | r1_lattices(sK7,sK4(sK7,X0_56),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_20,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_983,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_984,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_983])).

cnf(c_988,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_984,c_37,c_35,c_34])).

cnf(c_989,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_988])).

cnf(c_2791,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | ~ r1_lattices(sK7,X0_55,sK5(sK7,X0_56,X0_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_989])).

cnf(c_3343,plain,
    ( k15_lattice3(sK7,X0_56) = X0_55
    | r4_lattice3(sK7,X0_55,X0_56) != iProver_top
    | r1_lattices(sK7,X0_55,sK5(sK7,X0_56,X0_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2791])).

cnf(c_4073,plain,
    ( k15_lattice3(sK7,X0_56) = sK4(sK7,X1_56)
    | r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X1_56)),X1_56) != iProver_top
    | r4_lattice3(sK7,sK4(sK7,X1_56),X0_56) != iProver_top
    | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X1_56)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,X1_56),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_3343])).

cnf(c_4075,plain,
    ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
    | r4_lattice3(sK7,sK5(sK7,sK9,sK4(sK7,sK9)),sK9) != iProver_top
    | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK4(sK7,sK9)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4073])).

cnf(c_21,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK5(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_959,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK5(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_960,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_37,c_35,c_34])).

cnf(c_965,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_964])).

cnf(c_2792,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | r4_lattice3(sK7,sK5(sK7,X0_56,X0_55),X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_965])).

cnf(c_4052,plain,
    ( r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X0_56)),X0_56)
    | ~ r4_lattice3(sK7,sK4(sK7,X0_56),X0_56)
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_4053,plain,
    ( k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56)
    | r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X0_56)),X0_56) = iProver_top
    | r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) != iProver_top
    | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4052])).

cnf(c_4055,plain,
    ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
    | r4_lattice3(sK7,sK5(sK7,sK9,sK4(sK7,sK9)),sK9) = iProver_top
    | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
    | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4053])).

cnf(c_22,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_935,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X2,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,X2) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_936,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_940,plain,
    ( m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r4_lattice3(sK7,X0,X1)
    | k15_lattice3(sK7,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_37,c_35,c_34])).

cnf(c_941,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
    | k15_lattice3(sK7,X1) = X0 ),
    inference(renaming,[status(thm)],[c_940])).

cnf(c_2793,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0_56,X0_55),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_941])).

cnf(c_4015,plain,
    ( ~ r4_lattice3(sK7,sK4(sK7,X0_56),X0_56)
    | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X0_56)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56) ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_4016,plain,
    ( k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56)
    | r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) != iProver_top
    | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X0_56)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4015])).

cnf(c_4018,plain,
    ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
    | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
    | m1_subset_1(sK5(sK7,sK9,sK4(sK7,sK9)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4016])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1134,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_37])).

cnf(c_1135,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1134])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r4_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1135,c_34])).

cnf(c_1140,plain,
    ( ~ r4_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1139])).

cnf(c_2786,plain,
    ( ~ r4_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,X1_55,X0_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1140])).

cnf(c_3996,plain,
    ( ~ r4_lattice3(sK7,k15_lattice3(sK7,sK9),X0_56)
    | r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
    | ~ r2_hidden(sK8,X0_56)
    | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_3998,plain,
    ( ~ r4_lattice3(sK7,k15_lattice3(sK7,sK9),sK9)
    | r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
    | ~ r2_hidden(sK8,sK9)
    | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3996])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_446,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_450,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_2,c_1])).

cnf(c_734,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_450,c_36])).

cnf(c_735,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_37,c_34])).

cnf(c_740,plain,
    ( ~ r1_lattices(sK7,X0,X1)
    | r3_lattices(sK7,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_2801,plain,
    ( ~ r1_lattices(sK7,X0_55,X1_55)
    | r3_lattices(sK7,X0_55,X1_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_740])).

cnf(c_3793,plain,
    ( ~ r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
    | r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
    | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(c_2810,plain,
    ( ~ m1_subset_1(X0_55,X0_57)
    | m1_subset_1(X1_55,X0_57)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3630,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
    | X0_55 != sK4(sK7,X0_56) ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_3696,plain,
    ( m1_subset_1(k15_lattice3(sK7,X0_56),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,X1_56),u1_struct_0(sK7))
    | k15_lattice3(sK7,X0_56) != sK4(sK7,X1_56) ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_3698,plain,
    ( m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7))
    | k15_lattice3(sK7,sK9) != sK4(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_3696])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1224,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_37])).

cnf(c_1225,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1224])).

cnf(c_1229,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r3_lattice3(sK7,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1225,c_34])).

cnf(c_1230,plain,
    ( ~ r3_lattice3(sK7,X0,X1)
    | r1_lattices(sK7,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1229])).

cnf(c_2782,plain,
    ( ~ r3_lattice3(sK7,X0_55,X0_56)
    | r1_lattices(sK7,X0_55,X1_55)
    | ~ r2_hidden(X1_55,X0_56)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1230])).

cnf(c_3665,plain,
    ( ~ r3_lattice3(sK7,k16_lattice3(sK7,sK9),X0_56)
    | r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | ~ r2_hidden(sK8,X0_56)
    | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_3670,plain,
    ( ~ r3_lattice3(sK7,k16_lattice3(sK7,sK9),sK9)
    | r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | ~ r2_hidden(sK8,sK9)
    | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3665])).

cnf(c_3596,plain,
    ( ~ r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(c_18,plain,
    ( r4_lattice3(X0,sK4(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1092,plain,
    ( r4_lattice3(X0,sK4(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_1093,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0),X0)
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1092])).

cnf(c_1097,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_35,c_34])).

cnf(c_2788,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_1097])).

cnf(c_2864,plain,
    ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_2866,plain,
    ( r4_lattice3(sK7,sK4(sK7,sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2864])).

cnf(c_19,plain,
    ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1077,plain,
    ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_37])).

cnf(c_1078,plain,
    ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1077])).

cnf(c_1082,plain,
    ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1078,c_35,c_34])).

cnf(c_2789,plain,
    ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1082])).

cnf(c_2861,plain,
    ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2789])).

cnf(c_2863,plain,
    ( m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_2862,plain,
    ( m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_25,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1062,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_1063,plain,
    ( m1_subset_1(k16_lattice3(sK7,X0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7) ),
    inference(unflattening,[status(thm)],[c_1062])).

cnf(c_1067,plain,
    ( m1_subset_1(k16_lattice3(sK7,X0),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1063,c_34])).

cnf(c_2790,plain,
    ( m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1067])).

cnf(c_2859,plain,
    ( m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_24,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_893,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_894,plain,
    ( r4_lattice3(sK7,k15_lattice3(sK7,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_898,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
    | r4_lattice3(sK7,k15_lattice3(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_37,c_35,c_34])).

cnf(c_899,plain,
    ( r4_lattice3(sK7,k15_lattice3(sK7,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_898])).

cnf(c_2795,plain,
    ( r4_lattice3(sK7,k15_lattice3(sK7,X0_56),X0_56)
    | ~ m1_subset_1(k15_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_899])).

cnf(c_2844,plain,
    ( r4_lattice3(sK7,k15_lattice3(sK7,sK9),sK9)
    | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2795])).

cnf(c_30,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_214,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_25])).

cnf(c_782,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_36])).

cnf(c_783,plain,
    ( r3_lattice3(sK7,k16_lattice3(sK7,X0),X0)
    | ~ v4_lattice3(sK7)
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_787,plain,
    ( r3_lattice3(sK7,k16_lattice3(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_783,c_37,c_35,c_34])).

cnf(c_2799,plain,
    ( r3_lattice3(sK7,k16_lattice3(sK7,X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_787])).

cnf(c_2832,plain,
    ( r3_lattice3(sK7,k16_lattice3(sK7,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_2799])).

cnf(c_31,negated_conjecture,
    ( ~ r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
    | ~ r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK8,sK9) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4075,c_4055,c_4018,c_3998,c_3793,c_3698,c_3670,c_3596,c_2866,c_2863,c_2862,c_2859,c_2844,c_2832,c_31,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.78/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/0.99  
% 1.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.78/0.99  
% 1.78/0.99  ------  iProver source info
% 1.78/0.99  
% 1.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.78/0.99  git: non_committed_changes: false
% 1.78/0.99  git: last_make_outside_of_git: false
% 1.78/0.99  
% 1.78/0.99  ------ 
% 1.78/0.99  
% 1.78/0.99  ------ Input Options
% 1.78/0.99  
% 1.78/0.99  --out_options                           all
% 1.78/0.99  --tptp_safe_out                         true
% 1.78/0.99  --problem_path                          ""
% 1.78/0.99  --include_path                          ""
% 1.78/0.99  --clausifier                            res/vclausify_rel
% 1.78/0.99  --clausifier_options                    --mode clausify
% 1.78/0.99  --stdin                                 false
% 1.78/0.99  --stats_out                             all
% 1.78/0.99  
% 1.78/0.99  ------ General Options
% 1.78/0.99  
% 1.78/0.99  --fof                                   false
% 1.78/0.99  --time_out_real                         305.
% 1.78/0.99  --time_out_virtual                      -1.
% 1.78/0.99  --symbol_type_check                     false
% 1.78/0.99  --clausify_out                          false
% 1.78/0.99  --sig_cnt_out                           false
% 1.78/0.99  --trig_cnt_out                          false
% 1.78/0.99  --trig_cnt_out_tolerance                1.
% 1.78/0.99  --trig_cnt_out_sk_spl                   false
% 1.78/0.99  --abstr_cl_out                          false
% 1.78/0.99  
% 1.78/0.99  ------ Global Options
% 1.78/0.99  
% 1.78/0.99  --schedule                              default
% 1.78/0.99  --add_important_lit                     false
% 1.78/0.99  --prop_solver_per_cl                    1000
% 1.78/0.99  --min_unsat_core                        false
% 1.78/0.99  --soft_assumptions                      false
% 1.78/0.99  --soft_lemma_size                       3
% 1.78/0.99  --prop_impl_unit_size                   0
% 1.78/0.99  --prop_impl_unit                        []
% 1.78/0.99  --share_sel_clauses                     true
% 1.78/0.99  --reset_solvers                         false
% 1.78/0.99  --bc_imp_inh                            [conj_cone]
% 1.78/0.99  --conj_cone_tolerance                   3.
% 1.78/0.99  --extra_neg_conj                        none
% 1.78/0.99  --large_theory_mode                     true
% 1.78/0.99  --prolific_symb_bound                   200
% 1.78/0.99  --lt_threshold                          2000
% 1.78/0.99  --clause_weak_htbl                      true
% 1.78/0.99  --gc_record_bc_elim                     false
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing Options
% 1.78/0.99  
% 1.78/0.99  --preprocessing_flag                    true
% 1.78/0.99  --time_out_prep_mult                    0.1
% 1.78/0.99  --splitting_mode                        input
% 1.78/0.99  --splitting_grd                         true
% 1.78/0.99  --splitting_cvd                         false
% 1.78/0.99  --splitting_cvd_svl                     false
% 1.78/0.99  --splitting_nvd                         32
% 1.78/0.99  --sub_typing                            true
% 1.78/0.99  --prep_gs_sim                           true
% 1.78/0.99  --prep_unflatten                        true
% 1.78/0.99  --prep_res_sim                          true
% 1.78/0.99  --prep_upred                            true
% 1.78/0.99  --prep_sem_filter                       exhaustive
% 1.78/0.99  --prep_sem_filter_out                   false
% 1.78/0.99  --pred_elim                             true
% 1.78/0.99  --res_sim_input                         true
% 1.78/0.99  --eq_ax_congr_red                       true
% 1.78/0.99  --pure_diseq_elim                       true
% 1.78/0.99  --brand_transform                       false
% 1.78/0.99  --non_eq_to_eq                          false
% 1.78/0.99  --prep_def_merge                        true
% 1.78/0.99  --prep_def_merge_prop_impl              false
% 1.78/0.99  --prep_def_merge_mbd                    true
% 1.78/0.99  --prep_def_merge_tr_red                 false
% 1.78/0.99  --prep_def_merge_tr_cl                  false
% 1.78/0.99  --smt_preprocessing                     true
% 1.78/0.99  --smt_ac_axioms                         fast
% 1.78/0.99  --preprocessed_out                      false
% 1.78/0.99  --preprocessed_stats                    false
% 1.78/0.99  
% 1.78/0.99  ------ Abstraction refinement Options
% 1.78/0.99  
% 1.78/0.99  --abstr_ref                             []
% 1.78/0.99  --abstr_ref_prep                        false
% 1.78/0.99  --abstr_ref_until_sat                   false
% 1.78/0.99  --abstr_ref_sig_restrict                funpre
% 1.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/0.99  --abstr_ref_under                       []
% 1.78/0.99  
% 1.78/0.99  ------ SAT Options
% 1.78/0.99  
% 1.78/0.99  --sat_mode                              false
% 1.78/0.99  --sat_fm_restart_options                ""
% 1.78/0.99  --sat_gr_def                            false
% 1.78/0.99  --sat_epr_types                         true
% 1.78/0.99  --sat_non_cyclic_types                  false
% 1.78/0.99  --sat_finite_models                     false
% 1.78/0.99  --sat_fm_lemmas                         false
% 1.78/0.99  --sat_fm_prep                           false
% 1.78/0.99  --sat_fm_uc_incr                        true
% 1.78/0.99  --sat_out_model                         small
% 1.78/0.99  --sat_out_clauses                       false
% 1.78/0.99  
% 1.78/0.99  ------ QBF Options
% 1.78/0.99  
% 1.78/0.99  --qbf_mode                              false
% 1.78/0.99  --qbf_elim_univ                         false
% 1.78/0.99  --qbf_dom_inst                          none
% 1.78/0.99  --qbf_dom_pre_inst                      false
% 1.78/0.99  --qbf_sk_in                             false
% 1.78/0.99  --qbf_pred_elim                         true
% 1.78/0.99  --qbf_split                             512
% 1.78/0.99  
% 1.78/0.99  ------ BMC1 Options
% 1.78/0.99  
% 1.78/0.99  --bmc1_incremental                      false
% 1.78/0.99  --bmc1_axioms                           reachable_all
% 1.78/0.99  --bmc1_min_bound                        0
% 1.78/0.99  --bmc1_max_bound                        -1
% 1.78/0.99  --bmc1_max_bound_default                -1
% 1.78/0.99  --bmc1_symbol_reachability              true
% 1.78/0.99  --bmc1_property_lemmas                  false
% 1.78/0.99  --bmc1_k_induction                      false
% 1.78/0.99  --bmc1_non_equiv_states                 false
% 1.78/0.99  --bmc1_deadlock                         false
% 1.78/0.99  --bmc1_ucm                              false
% 1.78/0.99  --bmc1_add_unsat_core                   none
% 1.78/0.99  --bmc1_unsat_core_children              false
% 1.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/0.99  --bmc1_out_stat                         full
% 1.78/0.99  --bmc1_ground_init                      false
% 1.78/0.99  --bmc1_pre_inst_next_state              false
% 1.78/0.99  --bmc1_pre_inst_state                   false
% 1.78/0.99  --bmc1_pre_inst_reach_state             false
% 1.78/0.99  --bmc1_out_unsat_core                   false
% 1.78/0.99  --bmc1_aig_witness_out                  false
% 1.78/0.99  --bmc1_verbose                          false
% 1.78/0.99  --bmc1_dump_clauses_tptp                false
% 1.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.78/0.99  --bmc1_dump_file                        -
% 1.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.78/0.99  --bmc1_ucm_extend_mode                  1
% 1.78/0.99  --bmc1_ucm_init_mode                    2
% 1.78/0.99  --bmc1_ucm_cone_mode                    none
% 1.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.78/0.99  --bmc1_ucm_relax_model                  4
% 1.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/0.99  --bmc1_ucm_layered_model                none
% 1.78/0.99  --bmc1_ucm_max_lemma_size               10
% 1.78/0.99  
% 1.78/0.99  ------ AIG Options
% 1.78/0.99  
% 1.78/0.99  --aig_mode                              false
% 1.78/0.99  
% 1.78/0.99  ------ Instantiation Options
% 1.78/0.99  
% 1.78/0.99  --instantiation_flag                    true
% 1.78/0.99  --inst_sos_flag                         false
% 1.78/0.99  --inst_sos_phase                        true
% 1.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/0.99  --inst_lit_sel_side                     num_symb
% 1.78/0.99  --inst_solver_per_active                1400
% 1.78/0.99  --inst_solver_calls_frac                1.
% 1.78/0.99  --inst_passive_queue_type               priority_queues
% 1.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/0.99  --inst_passive_queues_freq              [25;2]
% 1.78/0.99  --inst_dismatching                      true
% 1.78/0.99  --inst_eager_unprocessed_to_passive     true
% 1.78/0.99  --inst_prop_sim_given                   true
% 1.78/0.99  --inst_prop_sim_new                     false
% 1.78/0.99  --inst_subs_new                         false
% 1.78/0.99  --inst_eq_res_simp                      false
% 1.78/0.99  --inst_subs_given                       false
% 1.78/0.99  --inst_orphan_elimination               true
% 1.78/0.99  --inst_learning_loop_flag               true
% 1.78/0.99  --inst_learning_start                   3000
% 1.78/0.99  --inst_learning_factor                  2
% 1.78/0.99  --inst_start_prop_sim_after_learn       3
% 1.78/0.99  --inst_sel_renew                        solver
% 1.78/0.99  --inst_lit_activity_flag                true
% 1.78/0.99  --inst_restr_to_given                   false
% 1.78/0.99  --inst_activity_threshold               500
% 1.78/0.99  --inst_out_proof                        true
% 1.78/0.99  
% 1.78/0.99  ------ Resolution Options
% 1.78/0.99  
% 1.78/0.99  --resolution_flag                       true
% 1.78/0.99  --res_lit_sel                           adaptive
% 1.78/0.99  --res_lit_sel_side                      none
% 1.78/0.99  --res_ordering                          kbo
% 1.78/0.99  --res_to_prop_solver                    active
% 1.78/0.99  --res_prop_simpl_new                    false
% 1.78/0.99  --res_prop_simpl_given                  true
% 1.78/0.99  --res_passive_queue_type                priority_queues
% 1.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/0.99  --res_passive_queues_freq               [15;5]
% 1.78/0.99  --res_forward_subs                      full
% 1.78/0.99  --res_backward_subs                     full
% 1.78/0.99  --res_forward_subs_resolution           true
% 1.78/0.99  --res_backward_subs_resolution          true
% 1.78/0.99  --res_orphan_elimination                true
% 1.78/0.99  --res_time_limit                        2.
% 1.78/0.99  --res_out_proof                         true
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Options
% 1.78/0.99  
% 1.78/0.99  --superposition_flag                    true
% 1.78/0.99  --sup_passive_queue_type                priority_queues
% 1.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.78/0.99  --demod_completeness_check              fast
% 1.78/0.99  --demod_use_ground                      true
% 1.78/0.99  --sup_to_prop_solver                    passive
% 1.78/0.99  --sup_prop_simpl_new                    true
% 1.78/0.99  --sup_prop_simpl_given                  true
% 1.78/0.99  --sup_fun_splitting                     false
% 1.78/0.99  --sup_smt_interval                      50000
% 1.78/0.99  
% 1.78/0.99  ------ Superposition Simplification Setup
% 1.78/0.99  
% 1.78/0.99  --sup_indices_passive                   []
% 1.78/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_full_bw                           [BwDemod]
% 1.78/0.99  --sup_immed_triv                        [TrivRules]
% 1.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_immed_bw_main                     []
% 1.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/0.99  
% 1.78/0.99  ------ Combination Options
% 1.78/0.99  
% 1.78/0.99  --comb_res_mult                         3
% 1.78/0.99  --comb_sup_mult                         2
% 1.78/0.99  --comb_inst_mult                        10
% 1.78/0.99  
% 1.78/0.99  ------ Debug Options
% 1.78/0.99  
% 1.78/0.99  --dbg_backtrace                         false
% 1.78/0.99  --dbg_dump_prop_clauses                 false
% 1.78/0.99  --dbg_dump_prop_clauses_file            -
% 1.78/0.99  --dbg_out_stat                          false
% 1.78/0.99  ------ Parsing...
% 1.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.78/0.99  
% 1.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.78/0.99  ------ Proving...
% 1.78/0.99  ------ Problem Properties 
% 1.78/0.99  
% 1.78/0.99  
% 1.78/0.99  clauses                                 27
% 1.78/0.99  conjectures                             3
% 1.78/1.00  EPR                                     1
% 1.78/1.00  Horn                                    19
% 1.78/1.00  unary                                   6
% 1.78/1.00  binary                                  2
% 1.78/1.00  lits                                    80
% 1.78/1.00  lits eq                                 6
% 1.78/1.00  fd_pure                                 0
% 1.78/1.00  fd_pseudo                               0
% 1.78/1.00  fd_cond                                 0
% 1.78/1.00  fd_pseudo_cond                          6
% 1.78/1.00  AC symbols                              0
% 1.78/1.00  
% 1.78/1.00  ------ Schedule dynamic 5 is on 
% 1.78/1.00  
% 1.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  ------ 
% 1.78/1.00  Current options:
% 1.78/1.00  ------ 
% 1.78/1.00  
% 1.78/1.00  ------ Input Options
% 1.78/1.00  
% 1.78/1.00  --out_options                           all
% 1.78/1.00  --tptp_safe_out                         true
% 1.78/1.00  --problem_path                          ""
% 1.78/1.00  --include_path                          ""
% 1.78/1.00  --clausifier                            res/vclausify_rel
% 1.78/1.00  --clausifier_options                    --mode clausify
% 1.78/1.00  --stdin                                 false
% 1.78/1.00  --stats_out                             all
% 1.78/1.00  
% 1.78/1.00  ------ General Options
% 1.78/1.00  
% 1.78/1.00  --fof                                   false
% 1.78/1.00  --time_out_real                         305.
% 1.78/1.00  --time_out_virtual                      -1.
% 1.78/1.00  --symbol_type_check                     false
% 1.78/1.00  --clausify_out                          false
% 1.78/1.00  --sig_cnt_out                           false
% 1.78/1.00  --trig_cnt_out                          false
% 1.78/1.00  --trig_cnt_out_tolerance                1.
% 1.78/1.00  --trig_cnt_out_sk_spl                   false
% 1.78/1.00  --abstr_cl_out                          false
% 1.78/1.00  
% 1.78/1.00  ------ Global Options
% 1.78/1.00  
% 1.78/1.00  --schedule                              default
% 1.78/1.00  --add_important_lit                     false
% 1.78/1.00  --prop_solver_per_cl                    1000
% 1.78/1.00  --min_unsat_core                        false
% 1.78/1.00  --soft_assumptions                      false
% 1.78/1.00  --soft_lemma_size                       3
% 1.78/1.00  --prop_impl_unit_size                   0
% 1.78/1.00  --prop_impl_unit                        []
% 1.78/1.00  --share_sel_clauses                     true
% 1.78/1.00  --reset_solvers                         false
% 1.78/1.00  --bc_imp_inh                            [conj_cone]
% 1.78/1.00  --conj_cone_tolerance                   3.
% 1.78/1.00  --extra_neg_conj                        none
% 1.78/1.00  --large_theory_mode                     true
% 1.78/1.00  --prolific_symb_bound                   200
% 1.78/1.00  --lt_threshold                          2000
% 1.78/1.00  --clause_weak_htbl                      true
% 1.78/1.00  --gc_record_bc_elim                     false
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing Options
% 1.78/1.00  
% 1.78/1.00  --preprocessing_flag                    true
% 1.78/1.00  --time_out_prep_mult                    0.1
% 1.78/1.00  --splitting_mode                        input
% 1.78/1.00  --splitting_grd                         true
% 1.78/1.00  --splitting_cvd                         false
% 1.78/1.00  --splitting_cvd_svl                     false
% 1.78/1.00  --splitting_nvd                         32
% 1.78/1.00  --sub_typing                            true
% 1.78/1.00  --prep_gs_sim                           true
% 1.78/1.00  --prep_unflatten                        true
% 1.78/1.00  --prep_res_sim                          true
% 1.78/1.00  --prep_upred                            true
% 1.78/1.00  --prep_sem_filter                       exhaustive
% 1.78/1.00  --prep_sem_filter_out                   false
% 1.78/1.00  --pred_elim                             true
% 1.78/1.00  --res_sim_input                         true
% 1.78/1.00  --eq_ax_congr_red                       true
% 1.78/1.00  --pure_diseq_elim                       true
% 1.78/1.00  --brand_transform                       false
% 1.78/1.00  --non_eq_to_eq                          false
% 1.78/1.00  --prep_def_merge                        true
% 1.78/1.00  --prep_def_merge_prop_impl              false
% 1.78/1.00  --prep_def_merge_mbd                    true
% 1.78/1.00  --prep_def_merge_tr_red                 false
% 1.78/1.00  --prep_def_merge_tr_cl                  false
% 1.78/1.00  --smt_preprocessing                     true
% 1.78/1.00  --smt_ac_axioms                         fast
% 1.78/1.00  --preprocessed_out                      false
% 1.78/1.00  --preprocessed_stats                    false
% 1.78/1.00  
% 1.78/1.00  ------ Abstraction refinement Options
% 1.78/1.00  
% 1.78/1.00  --abstr_ref                             []
% 1.78/1.00  --abstr_ref_prep                        false
% 1.78/1.00  --abstr_ref_until_sat                   false
% 1.78/1.00  --abstr_ref_sig_restrict                funpre
% 1.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/1.00  --abstr_ref_under                       []
% 1.78/1.00  
% 1.78/1.00  ------ SAT Options
% 1.78/1.00  
% 1.78/1.00  --sat_mode                              false
% 1.78/1.00  --sat_fm_restart_options                ""
% 1.78/1.00  --sat_gr_def                            false
% 1.78/1.00  --sat_epr_types                         true
% 1.78/1.00  --sat_non_cyclic_types                  false
% 1.78/1.00  --sat_finite_models                     false
% 1.78/1.00  --sat_fm_lemmas                         false
% 1.78/1.00  --sat_fm_prep                           false
% 1.78/1.00  --sat_fm_uc_incr                        true
% 1.78/1.00  --sat_out_model                         small
% 1.78/1.00  --sat_out_clauses                       false
% 1.78/1.00  
% 1.78/1.00  ------ QBF Options
% 1.78/1.00  
% 1.78/1.00  --qbf_mode                              false
% 1.78/1.00  --qbf_elim_univ                         false
% 1.78/1.00  --qbf_dom_inst                          none
% 1.78/1.00  --qbf_dom_pre_inst                      false
% 1.78/1.00  --qbf_sk_in                             false
% 1.78/1.00  --qbf_pred_elim                         true
% 1.78/1.00  --qbf_split                             512
% 1.78/1.00  
% 1.78/1.00  ------ BMC1 Options
% 1.78/1.00  
% 1.78/1.00  --bmc1_incremental                      false
% 1.78/1.00  --bmc1_axioms                           reachable_all
% 1.78/1.00  --bmc1_min_bound                        0
% 1.78/1.00  --bmc1_max_bound                        -1
% 1.78/1.00  --bmc1_max_bound_default                -1
% 1.78/1.00  --bmc1_symbol_reachability              true
% 1.78/1.00  --bmc1_property_lemmas                  false
% 1.78/1.00  --bmc1_k_induction                      false
% 1.78/1.00  --bmc1_non_equiv_states                 false
% 1.78/1.00  --bmc1_deadlock                         false
% 1.78/1.00  --bmc1_ucm                              false
% 1.78/1.00  --bmc1_add_unsat_core                   none
% 1.78/1.00  --bmc1_unsat_core_children              false
% 1.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/1.00  --bmc1_out_stat                         full
% 1.78/1.00  --bmc1_ground_init                      false
% 1.78/1.00  --bmc1_pre_inst_next_state              false
% 1.78/1.00  --bmc1_pre_inst_state                   false
% 1.78/1.00  --bmc1_pre_inst_reach_state             false
% 1.78/1.00  --bmc1_out_unsat_core                   false
% 1.78/1.00  --bmc1_aig_witness_out                  false
% 1.78/1.00  --bmc1_verbose                          false
% 1.78/1.00  --bmc1_dump_clauses_tptp                false
% 1.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.78/1.00  --bmc1_dump_file                        -
% 1.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.78/1.00  --bmc1_ucm_extend_mode                  1
% 1.78/1.00  --bmc1_ucm_init_mode                    2
% 1.78/1.00  --bmc1_ucm_cone_mode                    none
% 1.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.78/1.00  --bmc1_ucm_relax_model                  4
% 1.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/1.00  --bmc1_ucm_layered_model                none
% 1.78/1.00  --bmc1_ucm_max_lemma_size               10
% 1.78/1.00  
% 1.78/1.00  ------ AIG Options
% 1.78/1.00  
% 1.78/1.00  --aig_mode                              false
% 1.78/1.00  
% 1.78/1.00  ------ Instantiation Options
% 1.78/1.00  
% 1.78/1.00  --instantiation_flag                    true
% 1.78/1.00  --inst_sos_flag                         false
% 1.78/1.00  --inst_sos_phase                        true
% 1.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel_side                     none
% 1.78/1.00  --inst_solver_per_active                1400
% 1.78/1.00  --inst_solver_calls_frac                1.
% 1.78/1.00  --inst_passive_queue_type               priority_queues
% 1.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/1.00  --inst_passive_queues_freq              [25;2]
% 1.78/1.00  --inst_dismatching                      true
% 1.78/1.00  --inst_eager_unprocessed_to_passive     true
% 1.78/1.00  --inst_prop_sim_given                   true
% 1.78/1.00  --inst_prop_sim_new                     false
% 1.78/1.00  --inst_subs_new                         false
% 1.78/1.00  --inst_eq_res_simp                      false
% 1.78/1.00  --inst_subs_given                       false
% 1.78/1.00  --inst_orphan_elimination               true
% 1.78/1.00  --inst_learning_loop_flag               true
% 1.78/1.00  --inst_learning_start                   3000
% 1.78/1.00  --inst_learning_factor                  2
% 1.78/1.00  --inst_start_prop_sim_after_learn       3
% 1.78/1.00  --inst_sel_renew                        solver
% 1.78/1.00  --inst_lit_activity_flag                true
% 1.78/1.00  --inst_restr_to_given                   false
% 1.78/1.00  --inst_activity_threshold               500
% 1.78/1.00  --inst_out_proof                        true
% 1.78/1.00  
% 1.78/1.00  ------ Resolution Options
% 1.78/1.00  
% 1.78/1.00  --resolution_flag                       false
% 1.78/1.00  --res_lit_sel                           adaptive
% 1.78/1.00  --res_lit_sel_side                      none
% 1.78/1.00  --res_ordering                          kbo
% 1.78/1.00  --res_to_prop_solver                    active
% 1.78/1.00  --res_prop_simpl_new                    false
% 1.78/1.00  --res_prop_simpl_given                  true
% 1.78/1.00  --res_passive_queue_type                priority_queues
% 1.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/1.00  --res_passive_queues_freq               [15;5]
% 1.78/1.00  --res_forward_subs                      full
% 1.78/1.00  --res_backward_subs                     full
% 1.78/1.00  --res_forward_subs_resolution           true
% 1.78/1.00  --res_backward_subs_resolution          true
% 1.78/1.00  --res_orphan_elimination                true
% 1.78/1.00  --res_time_limit                        2.
% 1.78/1.00  --res_out_proof                         true
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Options
% 1.78/1.00  
% 1.78/1.00  --superposition_flag                    true
% 1.78/1.00  --sup_passive_queue_type                priority_queues
% 1.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.78/1.00  --demod_completeness_check              fast
% 1.78/1.00  --demod_use_ground                      true
% 1.78/1.00  --sup_to_prop_solver                    passive
% 1.78/1.00  --sup_prop_simpl_new                    true
% 1.78/1.00  --sup_prop_simpl_given                  true
% 1.78/1.00  --sup_fun_splitting                     false
% 1.78/1.00  --sup_smt_interval                      50000
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Simplification Setup
% 1.78/1.00  
% 1.78/1.00  --sup_indices_passive                   []
% 1.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_full_bw                           [BwDemod]
% 1.78/1.00  --sup_immed_triv                        [TrivRules]
% 1.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_immed_bw_main                     []
% 1.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  
% 1.78/1.00  ------ Combination Options
% 1.78/1.00  
% 1.78/1.00  --comb_res_mult                         3
% 1.78/1.00  --comb_sup_mult                         2
% 1.78/1.00  --comb_inst_mult                        10
% 1.78/1.00  
% 1.78/1.00  ------ Debug Options
% 1.78/1.00  
% 1.78/1.00  --dbg_backtrace                         false
% 1.78/1.00  --dbg_dump_prop_clauses                 false
% 1.78/1.00  --dbg_dump_prop_clauses_file            -
% 1.78/1.00  --dbg_out_stat                          false
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  ------ Proving...
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  % SZS status Theorem for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  fof(f5,axiom,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f22,plain,(
% 1.78/1.00    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f5])).
% 1.78/1.00  
% 1.78/1.00  fof(f23,plain,(
% 1.78/1.00    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f41,plain,(
% 1.78/1.00    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f23])).
% 1.78/1.00  
% 1.78/1.00  fof(f42,plain,(
% 1.78/1.00    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(rectify,[],[f41])).
% 1.78/1.00  
% 1.78/1.00  fof(f45,plain,(
% 1.78/1.00    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK4(X0,X4),X4) & m1_subset_1(sK4(X0,X4),u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f44,plain,(
% 1.78/1.00    ( ! [X1] : (! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK3(X0,X2)) & r4_lattice3(X0,sK3(X0,X2),X1) & m1_subset_1(sK3(X0,X2),u1_struct_0(X0))))) )),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f43,plain,(
% 1.78/1.00    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK2(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f46,plain,(
% 1.78/1.00    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK3(X0,X2)) & r4_lattice3(X0,sK3(X0,X2),sK2(X0)) & m1_subset_1(sK3(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK4(X0,X4),X4) & m1_subset_1(sK4(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).
% 1.78/1.00  
% 1.78/1.00  fof(f77,plain,(
% 1.78/1.00    ( ! [X6,X4,X0] : (r1_lattices(X0,sK4(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f46])).
% 1.78/1.00  
% 1.78/1.00  fof(f9,conjecture,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f10,negated_conjecture,(
% 1.78/1.00    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.78/1.00    inference(negated_conjecture,[],[f9])).
% 1.78/1.00  
% 1.78/1.00  fof(f30,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f10])).
% 1.78/1.00  
% 1.78/1.00  fof(f31,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f30])).
% 1.78/1.00  
% 1.78/1.00  fof(f59,plain,(
% 1.78/1.00    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK9),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,sK9))) & r2_hidden(X1,sK9))) )),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f58,plain,(
% 1.78/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),sK8) | ~r3_lattices(X0,sK8,k15_lattice3(X0,X2))) & r2_hidden(sK8,X2)) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f57,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK7,k16_lattice3(sK7,X2),X1) | ~r3_lattices(sK7,X1,k15_lattice3(sK7,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK7))) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f60,plain,(
% 1.78/1.00    (((~r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8) | ~r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9))) & r2_hidden(sK8,sK9)) & m1_subset_1(sK8,u1_struct_0(sK7))) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f59,f58,f57])).
% 1.78/1.00  
% 1.78/1.00  fof(f92,plain,(
% 1.78/1.00    ~v2_struct_0(sK7)),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f94,plain,(
% 1.78/1.00    v4_lattice3(sK7)),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f95,plain,(
% 1.78/1.00    l3_lattices(sK7)),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f6,axiom,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f24,plain,(
% 1.78/1.00    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f6])).
% 1.78/1.00  
% 1.78/1.00  fof(f25,plain,(
% 1.78/1.00    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f24])).
% 1.78/1.00  
% 1.78/1.00  fof(f47,plain,(
% 1.78/1.00    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f25])).
% 1.78/1.00  
% 1.78/1.00  fof(f48,plain,(
% 1.78/1.00    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f47])).
% 1.78/1.00  
% 1.78/1.00  fof(f49,plain,(
% 1.78/1.00    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(rectify,[],[f48])).
% 1.78/1.00  
% 1.78/1.00  fof(f50,plain,(
% 1.78/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK5(X0,X1,X2)) & r4_lattice3(X0,sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f51,plain,(
% 1.78/1.00    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK5(X0,X1,X2)) & r4_lattice3(X0,sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 1.78/1.00  
% 1.78/1.00  fof(f85,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK5(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f51])).
% 1.78/1.00  
% 1.78/1.00  fof(f93,plain,(
% 1.78/1.00    v10_lattices(sK7)),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f84,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK5(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f51])).
% 1.78/1.00  
% 1.78/1.00  fof(f83,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f51])).
% 1.78/1.00  
% 1.78/1.00  fof(f4,axiom,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f20,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f4])).
% 1.78/1.00  
% 1.78/1.00  fof(f21,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f20])).
% 1.78/1.00  
% 1.78/1.00  fof(f37,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f21])).
% 1.78/1.00  
% 1.78/1.00  fof(f38,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(rectify,[],[f37])).
% 1.78/1.00  
% 1.78/1.00  fof(f39,plain,(
% 1.78/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f40,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 1.78/1.00  
% 1.78/1.00  fof(f71,plain,(
% 1.78/1.00    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f40])).
% 1.78/1.00  
% 1.78/1.00  fof(f1,axiom,(
% 1.78/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f11,plain,(
% 1.78/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.78/1.00    inference(pure_predicate_removal,[],[f1])).
% 1.78/1.00  
% 1.78/1.00  fof(f12,plain,(
% 1.78/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.78/1.00    inference(pure_predicate_removal,[],[f11])).
% 1.78/1.00  
% 1.78/1.00  fof(f13,plain,(
% 1.78/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.78/1.00    inference(pure_predicate_removal,[],[f12])).
% 1.78/1.00  
% 1.78/1.00  fof(f14,plain,(
% 1.78/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.78/1.00    inference(ennf_transformation,[],[f13])).
% 1.78/1.00  
% 1.78/1.00  fof(f15,plain,(
% 1.78/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.78/1.00    inference(flattening,[],[f14])).
% 1.78/1.00  
% 1.78/1.00  fof(f64,plain,(
% 1.78/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f15])).
% 1.78/1.00  
% 1.78/1.00  fof(f2,axiom,(
% 1.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f16,plain,(
% 1.78/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f2])).
% 1.78/1.00  
% 1.78/1.00  fof(f17,plain,(
% 1.78/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f16])).
% 1.78/1.00  
% 1.78/1.00  fof(f32,plain,(
% 1.78/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f17])).
% 1.78/1.00  
% 1.78/1.00  fof(f66,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f32])).
% 1.78/1.00  
% 1.78/1.00  fof(f62,plain,(
% 1.78/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f15])).
% 1.78/1.00  
% 1.78/1.00  fof(f63,plain,(
% 1.78/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f15])).
% 1.78/1.00  
% 1.78/1.00  fof(f3,axiom,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f18,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f3])).
% 1.78/1.00  
% 1.78/1.00  fof(f19,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f18])).
% 1.78/1.00  
% 1.78/1.00  fof(f33,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f19])).
% 1.78/1.00  
% 1.78/1.00  fof(f34,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(rectify,[],[f33])).
% 1.78/1.00  
% 1.78/1.00  fof(f35,plain,(
% 1.78/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f36,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 1.78/1.00  
% 1.78/1.00  fof(f67,plain,(
% 1.78/1.00    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f36])).
% 1.78/1.00  
% 1.78/1.00  fof(f76,plain,(
% 1.78/1.00    ( ! [X4,X0] : (r4_lattice3(X0,sK4(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f46])).
% 1.78/1.00  
% 1.78/1.00  fof(f75,plain,(
% 1.78/1.00    ( ! [X4,X0] : (m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f46])).
% 1.78/1.00  
% 1.78/1.00  fof(f7,axiom,(
% 1.78/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f26,plain,(
% 1.78/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f7])).
% 1.78/1.00  
% 1.78/1.00  fof(f27,plain,(
% 1.78/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f26])).
% 1.78/1.00  
% 1.78/1.00  fof(f86,plain,(
% 1.78/1.00    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f27])).
% 1.78/1.00  
% 1.78/1.00  fof(f81,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f51])).
% 1.78/1.00  
% 1.78/1.00  fof(f100,plain,(
% 1.78/1.00    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(equality_resolution,[],[f81])).
% 1.78/1.00  
% 1.78/1.00  fof(f8,axiom,(
% 1.78/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f28,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f8])).
% 1.78/1.00  
% 1.78/1.00  fof(f29,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f28])).
% 1.78/1.00  
% 1.78/1.00  fof(f52,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(nnf_transformation,[],[f29])).
% 1.78/1.00  
% 1.78/1.00  fof(f53,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(flattening,[],[f52])).
% 1.78/1.00  
% 1.78/1.00  fof(f54,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(rectify,[],[f53])).
% 1.78/1.00  
% 1.78/1.00  fof(f55,plain,(
% 1.78/1.00    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f56,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).
% 1.78/1.00  
% 1.78/1.00  fof(f87,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f56])).
% 1.78/1.00  
% 1.78/1.00  fof(f102,plain,(
% 1.78/1.00    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.78/1.00    inference(equality_resolution,[],[f87])).
% 1.78/1.00  
% 1.78/1.00  fof(f98,plain,(
% 1.78/1.00    ~r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8) | ~r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9))),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f97,plain,(
% 1.78/1.00    r2_hidden(sK8,sK9)),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  fof(f96,plain,(
% 1.78/1.00    m1_subset_1(sK8,u1_struct_0(sK7))),
% 1.78/1.00    inference(cnf_transformation,[],[f60])).
% 1.78/1.00  
% 1.78/1.00  cnf(c_17,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,sK4(X0,X2),X1)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_37,negated_conjecture,
% 1.78/1.00      ( ~ v2_struct_0(sK7) ),
% 1.78/1.00      inference(cnf_transformation,[],[f92]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1107,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,sK4(X0,X2),X1)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1108,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,sK4(sK7,X1),X0)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1107]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_35,negated_conjecture,
% 1.78/1.00      ( v4_lattice3(sK7) ),
% 1.78/1.00      inference(cnf_transformation,[],[f94]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_34,negated_conjecture,
% 1.78/1.00      ( l3_lattices(sK7) ),
% 1.78/1.00      inference(cnf_transformation,[],[f95]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1112,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,sK4(sK7,X1),X0)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1108,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2787,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | r1_lattices(sK7,sK4(sK7,X0_56),X0_55)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1112]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3347,plain,
% 1.78/1.00      ( r4_lattice3(sK7,X0_55,X0_56) != iProver_top
% 1.78/1.00      | r1_lattices(sK7,sK4(sK7,X0_56),X0_55) = iProver_top
% 1.78/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_20,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | ~ r1_lattices(X0,X1,sK5(X0,X2,X1))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1 ),
% 1.78/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_36,negated_conjecture,
% 1.78/1.00      ( v10_lattices(sK7) ),
% 1.78/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_983,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | ~ r1_lattices(X0,X1,sK5(X0,X2,X1))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_984,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_983]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_988,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
% 1.78/1.00      | ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_984,c_37,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_989,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | ~ r1_lattices(sK7,X0,sK5(sK7,X1,X0))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_988]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2791,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | ~ r1_lattices(sK7,X0_55,sK5(sK7,X0_56,X0_55))
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) = X0_55 ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_989]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3343,plain,
% 1.78/1.00      ( k15_lattice3(sK7,X0_56) = X0_55
% 1.78/1.00      | r4_lattice3(sK7,X0_55,X0_56) != iProver_top
% 1.78/1.00      | r1_lattices(sK7,X0_55,sK5(sK7,X0_56,X0_55)) != iProver_top
% 1.78/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2791]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4073,plain,
% 1.78/1.00      ( k15_lattice3(sK7,X0_56) = sK4(sK7,X1_56)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X1_56)),X1_56) != iProver_top
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,X1_56),X0_56) != iProver_top
% 1.78/1.00      | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X1_56)),u1_struct_0(sK7)) != iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,X1_56),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_3347,c_3343]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4075,plain,
% 1.78/1.00      ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,sK9,sK4(sK7,sK9)),sK9) != iProver_top
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
% 1.78/1.00      | m1_subset_1(sK5(sK7,sK9,sK4(sK7,sK9)),u1_struct_0(sK7)) != iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_4073]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_21,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r4_lattice3(X0,sK5(X0,X2,X1),X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1 ),
% 1.78/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_959,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r4_lattice3(X0,sK5(X0,X2,X1),X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_960,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_959]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_964,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
% 1.78/1.00      | ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_960,c_37,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_965,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X1,X0),X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_964]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2792,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X0_56,X0_55),X0_56)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) = X0_55 ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_965]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4052,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X0_56)),X0_56)
% 1.78/1.00      | ~ r4_lattice3(sK7,sK4(sK7,X0_56),X0_56)
% 1.78/1.00      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2792]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4053,plain,
% 1.78/1.00      ( k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,X0_56,sK4(sK7,X0_56)),X0_56) = iProver_top
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) != iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4052]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4055,plain,
% 1.78/1.00      ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
% 1.78/1.00      | r4_lattice3(sK7,sK5(sK7,sK9,sK4(sK7,sK9)),sK9) = iProver_top
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_4053]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_22,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | m1_subset_1(sK5(X0,X2,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1 ),
% 1.78/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_935,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | m1_subset_1(sK5(X0,X2,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | k15_lattice3(X0,X2) = X1
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_936,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_935]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_940,plain,
% 1.78/1.00      ( m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_936,c_37,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_941,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X1) = X0 ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_940]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2793,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | m1_subset_1(sK5(sK7,X0_56,X0_55),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) = X0_55 ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_941]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4015,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,sK4(sK7,X0_56),X0_56)
% 1.78/1.00      | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X0_56)),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2793]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4016,plain,
% 1.78/1.00      ( k15_lattice3(sK7,X0_56) = sK4(sK7,X0_56)
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) != iProver_top
% 1.78/1.00      | m1_subset_1(sK5(sK7,X0_56,sK4(sK7,X0_56)),u1_struct_0(sK7)) = iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4015]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4018,plain,
% 1.78/1.00      ( k15_lattice3(sK7,sK9) = sK4(sK7,sK9)
% 1.78/1.00      | r4_lattice3(sK7,sK4(sK7,sK9),sK9) != iProver_top
% 1.78/1.00      | m1_subset_1(sK5(sK7,sK9,sK4(sK7,sK9)),u1_struct_0(sK7)) = iProver_top
% 1.78/1.00      | m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) != iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_4016]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_13,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,X3,X1)
% 1.78/1.00      | ~ r2_hidden(X3,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1134,plain,
% 1.78/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,X3,X1)
% 1.78/1.00      | ~ r2_hidden(X3,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1135,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,X2,X0)
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1134]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1139,plain,
% 1.78/1.00      ( ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | r1_lattices(sK7,X2,X0)
% 1.78/1.00      | ~ r4_lattice3(sK7,X0,X1) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1135,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1140,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,X2,X0)
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_1139]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2786,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | r1_lattices(sK7,X1_55,X0_55)
% 1.78/1.00      | ~ r2_hidden(X1_55,X0_56)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1140]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3996,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,k15_lattice3(sK7,sK9),X0_56)
% 1.78/1.00      | r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
% 1.78/1.00      | ~ r2_hidden(sK8,X0_56)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2786]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3998,plain,
% 1.78/1.00      ( ~ r4_lattice3(sK7,k15_lattice3(sK7,sK9),sK9)
% 1.78/1.00      | r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
% 1.78/1.00      | ~ r2_hidden(sK8,sK9)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_3996]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_0,plain,
% 1.78/1.00      ( ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0)
% 1.78/1.00      | v9_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4,plain,
% 1.78/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.78/1.00      | r3_lattices(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v6_lattices(X0)
% 1.78/1.00      | ~ v8_lattices(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v9_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_446,plain,
% 1.78/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.78/1.00      | r3_lattices(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ v6_lattices(X0)
% 1.78/1.00      | ~ v8_lattices(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2,plain,
% 1.78/1.00      ( v6_lattices(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1,plain,
% 1.78/1.00      ( v8_lattices(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_450,plain,
% 1.78/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.78/1.00      | r3_lattices(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_446,c_2,c_1]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_734,plain,
% 1.78/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.78/1.00      | r3_lattices(X0,X1,X2)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_450,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_735,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 1.78/1.00      | r3_lattices(sK7,X0,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_734]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_739,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 1.78/1.00      | r3_lattices(sK7,X0,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_735,c_37,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_740,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,X0,X1)
% 1.78/1.00      | r3_lattices(sK7,X0,X1)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_739]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2801,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,X0_55,X1_55)
% 1.78/1.00      | r3_lattices(sK7,X0_55,X1_55)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_740]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3793,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
% 1.78/1.00      | r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9))
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2801]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2810,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0_55,X0_57)
% 1.78/1.00      | m1_subset_1(X1_55,X0_57)
% 1.78/1.00      | X1_55 != X0_55 ),
% 1.78/1.00      theory(equality) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3630,plain,
% 1.78/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7))
% 1.78/1.00      | X0_55 != sK4(sK7,X0_56) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2810]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3696,plain,
% 1.78/1.00      ( m1_subset_1(k15_lattice3(sK7,X0_56),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK4(sK7,X1_56),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,X0_56) != sK4(sK7,X1_56) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_3630]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3698,plain,
% 1.78/1.00      ( m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | k15_lattice3(sK7,sK9) != sK4(sK7,sK9) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_3696]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_9,plain,
% 1.78/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,X1,X3)
% 1.78/1.00      | ~ r2_hidden(X3,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1224,plain,
% 1.78/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 1.78/1.00      | r1_lattices(X0,X1,X3)
% 1.78/1.00      | ~ r2_hidden(X3,X2)
% 1.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1225,plain,
% 1.78/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,X0,X2)
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1224]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1229,plain,
% 1.78/1.00      ( ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | r1_lattices(sK7,X0,X2)
% 1.78/1.00      | ~ r3_lattice3(sK7,X0,X1) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1225,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1230,plain,
% 1.78/1.00      ( ~ r3_lattice3(sK7,X0,X1)
% 1.78/1.00      | r1_lattices(sK7,X0,X2)
% 1.78/1.00      | ~ r2_hidden(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_1229]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2782,plain,
% 1.78/1.00      ( ~ r3_lattice3(sK7,X0_55,X0_56)
% 1.78/1.00      | r1_lattices(sK7,X0_55,X1_55)
% 1.78/1.00      | ~ r2_hidden(X1_55,X0_56)
% 1.78/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1230]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3665,plain,
% 1.78/1.00      ( ~ r3_lattice3(sK7,k16_lattice3(sK7,sK9),X0_56)
% 1.78/1.00      | r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
% 1.78/1.00      | ~ r2_hidden(sK8,X0_56)
% 1.78/1.00      | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2782]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3670,plain,
% 1.78/1.00      ( ~ r3_lattice3(sK7,k16_lattice3(sK7,sK9),sK9)
% 1.78/1.00      | r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
% 1.78/1.00      | ~ r2_hidden(sK8,sK9)
% 1.78/1.00      | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_3665]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3596,plain,
% 1.78/1.00      ( ~ r1_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
% 1.78/1.00      | r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
% 1.78/1.00      | ~ m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7))
% 1.78/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2801]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_18,plain,
% 1.78/1.00      ( r4_lattice3(X0,sK4(X0,X1),X1)
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1092,plain,
% 1.78/1.00      ( r4_lattice3(X0,sK4(X0,X1),X1)
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1093,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK4(sK7,X0),X0)
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1092]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1097,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK4(sK7,X0),X0) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1093,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2788,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1097]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2864,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK4(sK7,X0_56),X0_56) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2788]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2866,plain,
% 1.78/1.00      ( r4_lattice3(sK7,sK4(sK7,sK9),sK9) = iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2864]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_19,plain,
% 1.78/1.00      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1077,plain,
% 1.78/1.00      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1078,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1077]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1082,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1078,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2789,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1082]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2861,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,X0_56),u1_struct_0(sK7)) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2789]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2863,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) = iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2861]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2862,plain,
% 1.78/1.00      ( m1_subset_1(sK4(sK7,sK9),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2789]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_25,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f86]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1062,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1063,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(sK7,X0),u1_struct_0(sK7))
% 1.78/1.00      | ~ l3_lattices(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_1062]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1067,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(sK7,X0),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1063,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2790,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1067]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2859,plain,
% 1.78/1.00      ( m1_subset_1(k16_lattice3(sK7,sK9),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2790]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_24,plain,
% 1.78/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f100]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_893,plain,
% 1.78/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_894,plain,
% 1.78/1.00      ( r4_lattice3(sK7,k15_lattice3(sK7,X0),X0)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_893]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_898,plain,
% 1.78/1.00      ( ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7))
% 1.78/1.00      | r4_lattice3(sK7,k15_lattice3(sK7,X0),X0) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_894,c_37,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_899,plain,
% 1.78/1.00      ( r4_lattice3(sK7,k15_lattice3(sK7,X0),X0)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_898]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2795,plain,
% 1.78/1.00      ( r4_lattice3(sK7,k15_lattice3(sK7,X0_56),X0_56)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,X0_56),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_899]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2844,plain,
% 1.78/1.00      ( r4_lattice3(sK7,k15_lattice3(sK7,sK9),sK9)
% 1.78/1.00      | ~ m1_subset_1(k15_lattice3(sK7,sK9),u1_struct_0(sK7)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2795]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_30,plain,
% 1.78/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.78/1.00      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f102]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_214,plain,
% 1.78/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | ~ v10_lattices(X0) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_30,c_25]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_782,plain,
% 1.78/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.78/1.00      | ~ v4_lattice3(X0)
% 1.78/1.00      | ~ l3_lattices(X0)
% 1.78/1.00      | v2_struct_0(X0)
% 1.78/1.00      | sK7 != X0 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_214,c_36]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_783,plain,
% 1.78/1.00      ( r3_lattice3(sK7,k16_lattice3(sK7,X0),X0)
% 1.78/1.00      | ~ v4_lattice3(sK7)
% 1.78/1.00      | ~ l3_lattices(sK7)
% 1.78/1.00      | v2_struct_0(sK7) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_782]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_787,plain,
% 1.78/1.00      ( r3_lattice3(sK7,k16_lattice3(sK7,X0),X0) ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_783,c_37,c_35,c_34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2799,plain,
% 1.78/1.00      ( r3_lattice3(sK7,k16_lattice3(sK7,X0_56),X0_56) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_787]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2832,plain,
% 1.78/1.00      ( r3_lattice3(sK7,k16_lattice3(sK7,sK9),sK9) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_2799]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_31,negated_conjecture,
% 1.78/1.00      ( ~ r3_lattices(sK7,k16_lattice3(sK7,sK9),sK8)
% 1.78/1.00      | ~ r3_lattices(sK7,sK8,k15_lattice3(sK7,sK9)) ),
% 1.78/1.00      inference(cnf_transformation,[],[f98]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_32,negated_conjecture,
% 1.78/1.00      ( r2_hidden(sK8,sK9) ),
% 1.78/1.00      inference(cnf_transformation,[],[f97]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_33,negated_conjecture,
% 1.78/1.00      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 1.78/1.00      inference(cnf_transformation,[],[f96]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(contradiction,plain,
% 1.78/1.00      ( $false ),
% 1.78/1.00      inference(minisat,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_4075,c_4055,c_4018,c_3998,c_3793,c_3698,c_3670,c_3596,
% 1.78/1.00                 c_2866,c_2863,c_2862,c_2859,c_2844,c_2832,c_31,c_32,
% 1.78/1.00                 c_33]) ).
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  ------                               Statistics
% 1.78/1.00  
% 1.78/1.00  ------ General
% 1.78/1.00  
% 1.78/1.00  abstr_ref_over_cycles:                  0
% 1.78/1.00  abstr_ref_under_cycles:                 0
% 1.78/1.00  gc_basic_clause_elim:                   0
% 1.78/1.00  forced_gc_time:                         0
% 1.78/1.00  parsing_time:                           0.01
% 1.78/1.00  unif_index_cands_time:                  0.
% 1.78/1.00  unif_index_add_time:                    0.
% 1.78/1.00  orderings_time:                         0.
% 1.78/1.00  out_proof_time:                         0.011
% 1.78/1.00  total_time:                             0.164
% 1.78/1.00  num_of_symbols:                         61
% 1.78/1.00  num_of_terms:                           3442
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing
% 1.78/1.00  
% 1.78/1.00  num_of_splits:                          0
% 1.78/1.00  num_of_split_atoms:                     0
% 1.78/1.00  num_of_reused_defs:                     0
% 1.78/1.00  num_eq_ax_congr_red:                    62
% 1.78/1.00  num_of_sem_filtered_clauses:            1
% 1.78/1.00  num_of_subtypes:                        4
% 1.78/1.00  monotx_restored_types:                  0
% 1.78/1.00  sat_num_of_epr_types:                   0
% 1.78/1.00  sat_num_of_non_cyclic_types:            0
% 1.78/1.00  sat_guarded_non_collapsed_types:        1
% 1.78/1.00  num_pure_diseq_elim:                    0
% 1.78/1.00  simp_replaced_by:                       0
% 1.78/1.00  res_preprocessed:                       135
% 1.78/1.00  prep_upred:                             0
% 1.78/1.00  prep_unflattend:                        135
% 1.78/1.00  smt_new_axioms:                         0
% 1.78/1.00  pred_elim_cands:                        6
% 1.78/1.00  pred_elim:                              7
% 1.78/1.00  pred_elim_cl:                           10
% 1.78/1.00  pred_elim_cycles:                       12
% 1.78/1.00  merged_defs:                            0
% 1.78/1.00  merged_defs_ncl:                        0
% 1.78/1.00  bin_hyper_res:                          0
% 1.78/1.00  prep_cycles:                            4
% 1.78/1.00  pred_elim_time:                         0.049
% 1.78/1.00  splitting_time:                         0.
% 1.78/1.00  sem_filter_time:                        0.
% 1.78/1.00  monotx_time:                            0.
% 1.78/1.00  subtype_inf_time:                       0.
% 1.78/1.00  
% 1.78/1.00  ------ Problem properties
% 1.78/1.00  
% 1.78/1.00  clauses:                                27
% 1.78/1.00  conjectures:                            3
% 1.78/1.00  epr:                                    1
% 1.78/1.00  horn:                                   19
% 1.78/1.00  ground:                                 3
% 1.78/1.00  unary:                                  6
% 1.78/1.00  binary:                                 2
% 1.78/1.00  lits:                                   80
% 1.78/1.00  lits_eq:                                6
% 1.78/1.00  fd_pure:                                0
% 1.78/1.00  fd_pseudo:                              0
% 1.78/1.00  fd_cond:                                0
% 1.78/1.00  fd_pseudo_cond:                         6
% 1.78/1.00  ac_symbols:                             0
% 1.78/1.00  
% 1.78/1.00  ------ Propositional Solver
% 1.78/1.00  
% 1.78/1.00  prop_solver_calls:                      26
% 1.78/1.00  prop_fast_solver_calls:                 1686
% 1.78/1.00  smt_solver_calls:                       0
% 1.78/1.00  smt_fast_solver_calls:                  0
% 1.78/1.00  prop_num_of_clauses:                    1080
% 1.78/1.00  prop_preprocess_simplified:             5242
% 1.78/1.00  prop_fo_subsumed:                       86
% 1.78/1.00  prop_solver_time:                       0.
% 1.78/1.00  smt_solver_time:                        0.
% 1.78/1.00  smt_fast_solver_time:                   0.
% 1.78/1.00  prop_fast_solver_time:                  0.
% 1.78/1.00  prop_unsat_core_time:                   0.
% 1.78/1.00  
% 1.78/1.00  ------ QBF
% 1.78/1.00  
% 1.78/1.00  qbf_q_res:                              0
% 1.78/1.00  qbf_num_tautologies:                    0
% 1.78/1.00  qbf_prep_cycles:                        0
% 1.78/1.00  
% 1.78/1.00  ------ BMC1
% 1.78/1.00  
% 1.78/1.00  bmc1_current_bound:                     -1
% 1.78/1.00  bmc1_last_solved_bound:                 -1
% 1.78/1.00  bmc1_unsat_core_size:                   -1
% 1.78/1.00  bmc1_unsat_core_parents_size:           -1
% 1.78/1.00  bmc1_merge_next_fun:                    0
% 1.78/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.78/1.00  
% 1.78/1.00  ------ Instantiation
% 1.78/1.00  
% 1.78/1.00  inst_num_of_clauses:                    156
% 1.78/1.00  inst_num_in_passive:                    1
% 1.78/1.00  inst_num_in_active:                     101
% 1.78/1.00  inst_num_in_unprocessed:                54
% 1.78/1.00  inst_num_of_loops:                      128
% 1.78/1.00  inst_num_of_learning_restarts:          0
% 1.78/1.00  inst_num_moves_active_passive:          24
% 1.78/1.00  inst_lit_activity:                      0
% 1.78/1.00  inst_lit_activity_moves:                0
% 1.78/1.00  inst_num_tautologies:                   0
% 1.78/1.00  inst_num_prop_implied:                  0
% 1.78/1.00  inst_num_existing_simplified:           0
% 1.78/1.00  inst_num_eq_res_simplified:             0
% 1.78/1.00  inst_num_child_elim:                    0
% 1.78/1.00  inst_num_of_dismatching_blockings:      29
% 1.78/1.00  inst_num_of_non_proper_insts:           140
% 1.78/1.00  inst_num_of_duplicates:                 0
% 1.78/1.00  inst_inst_num_from_inst_to_res:         0
% 1.78/1.00  inst_dismatching_checking_time:         0.
% 1.78/1.00  
% 1.78/1.00  ------ Resolution
% 1.78/1.00  
% 1.78/1.00  res_num_of_clauses:                     0
% 1.78/1.00  res_num_in_passive:                     0
% 1.78/1.00  res_num_in_active:                      0
% 1.78/1.00  res_num_of_loops:                       139
% 1.78/1.00  res_forward_subset_subsumed:            16
% 1.78/1.00  res_backward_subset_subsumed:           0
% 1.78/1.00  res_forward_subsumed:                   0
% 1.78/1.00  res_backward_subsumed:                  0
% 1.78/1.00  res_forward_subsumption_resolution:     10
% 1.78/1.00  res_backward_subsumption_resolution:    1
% 1.78/1.00  res_clause_to_clause_subsumption:       158
% 1.78/1.00  res_orphan_elimination:                 0
% 1.78/1.00  res_tautology_del:                      9
% 1.78/1.00  res_num_eq_res_simplified:              0
% 1.78/1.00  res_num_sel_changes:                    0
% 1.78/1.00  res_moves_from_active_to_pass:          0
% 1.78/1.00  
% 1.78/1.00  ------ Superposition
% 1.78/1.00  
% 1.78/1.00  sup_time_total:                         0.
% 1.78/1.00  sup_time_generating:                    0.
% 1.78/1.00  sup_time_sim_full:                      0.
% 1.78/1.00  sup_time_sim_immed:                     0.
% 1.78/1.00  
% 1.78/1.00  sup_num_of_clauses:                     40
% 1.78/1.00  sup_num_in_active:                      24
% 1.78/1.00  sup_num_in_passive:                     16
% 1.78/1.00  sup_num_of_loops:                       24
% 1.78/1.00  sup_fw_superposition:                   10
% 1.78/1.00  sup_bw_superposition:                   3
% 1.78/1.00  sup_immediate_simplified:               0
% 1.78/1.00  sup_given_eliminated:                   0
% 1.78/1.00  comparisons_done:                       0
% 1.78/1.00  comparisons_avoided:                    0
% 1.78/1.00  
% 1.78/1.00  ------ Simplifications
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  sim_fw_subset_subsumed:                 0
% 1.78/1.00  sim_bw_subset_subsumed:                 0
% 1.78/1.00  sim_fw_subsumed:                        0
% 1.78/1.00  sim_bw_subsumed:                        0
% 1.78/1.00  sim_fw_subsumption_res:                 0
% 1.78/1.00  sim_bw_subsumption_res:                 0
% 1.78/1.00  sim_tautology_del:                      0
% 1.78/1.00  sim_eq_tautology_del:                   0
% 1.78/1.00  sim_eq_res_simp:                        0
% 1.78/1.00  sim_fw_demodulated:                     0
% 1.78/1.00  sim_bw_demodulated:                     0
% 1.78/1.00  sim_light_normalised:                   0
% 1.78/1.00  sim_joinable_taut:                      0
% 1.78/1.00  sim_joinable_simp:                      0
% 1.78/1.00  sim_ac_normalised:                      0
% 1.78/1.00  sim_smt_subsumption:                    0
% 1.78/1.00  
%------------------------------------------------------------------------------
