%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:14 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  239 (1009 expanded)
%              Number of clauses        :  163 ( 264 expanded)
%              Number of leaves         :   20 ( 308 expanded)
%              Depth                    :   24
%              Number of atoms          : 1234 (6909 expanded)
%              Number of equality atoms :  206 (1052 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK7) != X1
        & r3_lattice3(X0,X1,sK7)
        & r2_hidden(X1,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK6
            & r3_lattice3(X0,sK6,X2)
            & r2_hidden(sK6,X2) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK5,X2) != X1
              & r3_lattice3(sK5,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l3_lattices(sK5)
      & v4_lattice3(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k16_lattice3(sK5,sK7) != sK6
    & r3_lattice3(sK5,sK6,sK7)
    & r2_hidden(sK6,sK7)
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l3_lattices(sK5)
    & v4_lattice3(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f50,f49,f48])).

fof(f80,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

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
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
        & r3_lattice3(X0,sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK4(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f7,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

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
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
                & r4_lattice3(X0,sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK2(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    k16_lattice3(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    r3_lattice3(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3032,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_3031,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_4210,plain,
    ( X0_51 != X1_51
    | X1_51 = X0_51 ),
    inference(resolution,[status(thm)],[c_3032,c_3031])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK3(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1141,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | v2_struct_0(X1)
    | sK3(X0,X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_1142,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | v2_struct_0(sK5)
    | sK3(X0,sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1141])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1146,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | sK3(X0,sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_32])).

cnf(c_3002,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | sK3(X0_51,sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_1146])).

cnf(c_4954,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | X0_51 = sK3(X0_51,sK5,X0_52) ),
    inference(resolution,[status(thm)],[c_4210,c_3002])).

cnf(c_3033,plain,
    ( ~ r3_lattice3(X0_50,X0_51,X0_52)
    | r3_lattice3(X0_50,X1_51,X0_52)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_5388,plain,
    ( r3_lattice3(X0_50,X0_51,X0_52)
    | ~ r3_lattice3(X0_50,sK3(X0_51,sK5,X1_52),X0_52)
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X1_52)) ),
    inference(resolution,[status(thm)],[c_4954,c_3033])).

cnf(c_15,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_889,plain,
    ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_890,plain,
    ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_894,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | r3_lattice3(sK5,sK3(X0,sK5,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_32])).

cnf(c_895,plain,
    ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_894])).

cnf(c_3014,plain,
    ( r3_lattice3(sK5,sK3(X0_51,sK5,X0_52),X0_52)
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) ),
    inference(subtyping,[status(esa)],[c_895])).

cnf(c_7071,plain,
    ( r3_lattice3(sK5,X0_51,X0_52)
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) ),
    inference(resolution,[status(thm)],[c_5388,c_3014])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_991,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_992,plain,
    ( r4_lattice3(sK5,X0,X1)
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_996,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_992,c_32])).

cnf(c_997,plain,
    ( r4_lattice3(sK5,X0,X1)
    | r2_hidden(sK1(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_996])).

cnf(c_3009,plain,
    ( r4_lattice3(sK5,X0_51,X0_52)
    | r2_hidden(sK1(sK5,X0_51,X0_52),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_997])).

cnf(c_7214,plain,
    ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | r3_lattice3(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_7071,c_3009])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1033,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_29])).

cnf(c_1034,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattice3(sK5,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X2)
    | ~ r3_lattice3(sK5,X0,X2)
    | r1_lattices(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1034,c_32])).

cnf(c_1039,plain,
    ( r1_lattices(sK5,X0,X1)
    | ~ r3_lattice3(sK5,X0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1038])).

cnf(c_3007,plain,
    ( r1_lattices(sK5,X0_51,X1_51)
    | ~ r3_lattice3(sK5,X0_51,X0_52)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1039])).

cnf(c_7308,plain,
    ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_7214,c_3007])).

cnf(c_3035,plain,
    ( ~ m1_subset_1(X0_51,X0_53)
    | m1_subset_1(X1_51,X0_53)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_5386,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | m1_subset_1(X0_51,X0_53)
    | ~ m1_subset_1(sK3(X0_51,sK5,X0_52),X0_53) ),
    inference(resolution,[status(thm)],[c_4954,c_3035])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1123,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_1124,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1123])).

cnf(c_1128,plain,
    ( m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
    | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_32])).

cnf(c_1129,plain,
    ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1128])).

cnf(c_3003,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | m1_subset_1(sK3(X0_51,sK5,X0_52),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1129])).

cnf(c_6935,plain,
    ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_5386,c_3003])).

cnf(c_7094,plain,
    ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_6935,c_3009])).

cnf(c_11661,plain,
    ( ~ m1_subset_1(X1_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ r2_hidden(X1_51,X0_52)
    | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
    | r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7308,c_7094])).

cnf(c_11662,plain,
    ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_11661])).

cnf(c_4,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1012,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_1013,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_32])).

cnf(c_1018,plain,
    ( r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_1017])).

cnf(c_3008,plain,
    ( r4_lattice3(sK5,X0_51,X0_52)
    | ~ r1_lattices(sK5,sK1(sK5,X0_51,X0_52),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_1018])).

cnf(c_11695,plain,
    ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_11662,c_3008])).

cnf(c_11697,plain,
    ( r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
    | ~ r2_hidden(sK6,sK7)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11695])).

cnf(c_19,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_612,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_613,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
    | ~ r3_lattice3(sK5,X0,X1)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_32,c_31,c_29])).

cnf(c_618,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k16_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_3019,plain,
    ( ~ r3_lattice3(sK5,X0_51,X0_52)
    | r3_lattice3(sK5,sK4(sK5,X0_51,X0_52),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k16_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_3608,plain,
    ( k16_lattice3(sK5,X0_52) = X0_51
    | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
    | r3_lattice3(sK5,sK4(sK5,X0_51,X0_52),X0_52) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_20,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_588,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_589,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_593,plain,
    ( m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r3_lattice3(sK5,X0,X1)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_32,c_31,c_29])).

cnf(c_594,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
    | k16_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_593])).

cnf(c_3020,plain,
    ( ~ r3_lattice3(sK5,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5,X0_51,X0_52),u1_struct_0(sK5))
    | k16_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_594])).

cnf(c_3607,plain,
    ( k16_lattice3(sK5,X0_52) = X0_51
    | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,X0_51,X0_52),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3020])).

cnf(c_14,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_907,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_908,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ r3_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_32])).

cnf(c_913,plain,
    ( ~ r3_lattice3(sK5,X0,X1)
    | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_912])).

cnf(c_3013,plain,
    ( ~ r3_lattice3(sK5,X0_51,X0_52)
    | r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_913])).

cnf(c_3614,plain,
    ( r3_lattice3(sK5,X0_51,X0_52) != iProver_top
    | r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3013])).

cnf(c_24,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_504,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_505,plain,
    ( r3_lattices(sK5,X0,k15_lattice3(sK5,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X1)
    | r3_lattices(sK5,X0,k15_lattice3(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_32,c_31,c_29])).

cnf(c_510,plain,
    ( r3_lattices(sK5,X0,k15_lattice3(sK5,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_3024,plain,
    ( r3_lattices(sK5,X0_51,k15_lattice3(sK5,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_3603,plain,
    ( r3_lattices(sK5,X0_51,k15_lattice3(sK5,X0_52)) = iProver_top
    | r2_hidden(X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3024])).

cnf(c_18,plain,
    ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_636,plain,
    ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_637,plain,
    ( ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
    | ~ r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r3_lattice3(sK5,X0,X1)
    | ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
    | k16_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_32,c_31,c_29])).

cnf(c_642,plain,
    ( ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
    | ~ r3_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k16_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_641])).

cnf(c_3018,plain,
    ( ~ r3_lattices(sK5,sK4(sK5,X0_51,X0_52),X0_51)
    | ~ r3_lattice3(sK5,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k16_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_642])).

cnf(c_3609,plain,
    ( k16_lattice3(sK5,X0_52) = X0_51
    | r3_lattices(sK5,sK4(sK5,X0_51,X0_52),X0_51) != iProver_top
    | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3018])).

cnf(c_4389,plain,
    ( k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,X1_52)
    | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52) != iProver_top
    | r2_hidden(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),X1_52) != iProver_top
    | m1_subset_1(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,X1_52),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_3609])).

cnf(c_13,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_928,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_929,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_933,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_32])).

cnf(c_3012,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_52),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_3615,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_52),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3012])).

cnf(c_6768,plain,
    ( k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,X1_52)
    | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52) != iProver_top
    | r2_hidden(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),X1_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4389,c_3615,c_3607])).

cnf(c_6772,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
    | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
    | m1_subset_1(sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_6768])).

cnf(c_9834,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
    | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_6772])).

cnf(c_5337,plain,
    ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_5338,plain,
    ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5337])).

cnf(c_9839,plain,
    ( r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
    | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9834,c_5338])).

cnf(c_9840,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
    | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_9839])).

cnf(c_9848,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X0_52)
    | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3608,c_9840])).

cnf(c_9849,plain,
    ( ~ r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52)
    | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X0_52) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9848])).

cnf(c_9851,plain,
    ( ~ r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),sK7)
    | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = k16_lattice3(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_9849])).

cnf(c_7,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_943,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_944,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r4_lattice3(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_32])).

cnf(c_949,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r1_lattices(sK5,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_948])).

cnf(c_3011,plain,
    ( ~ r4_lattice3(sK5,X0_51,X0_52)
    | r1_lattices(sK5,X1_51,X0_51)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_6530,plain,
    ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | r1_lattices(sK5,X1_51,X0_51)
    | ~ r2_hidden(X1_51,a_2_1_lattice3(sK5,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_7838,plain,
    ( ~ r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),a_2_1_lattice3(sK5,X1_52))
    | r1_lattices(sK5,X0_51,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51))
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X1_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | ~ m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6530])).

cnf(c_7840,plain,
    ( ~ r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),a_2_1_lattice3(sK5,sK7))
    | r1_lattices(sK5,sK6,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6))
    | ~ r2_hidden(sK6,a_2_1_lattice3(sK5,sK7))
    | ~ m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7838])).

cnf(c_4374,plain,
    ( X0_51 != X1_51
    | k16_lattice3(sK5,X0_52) != X1_51
    | k16_lattice3(sK5,X0_52) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_4888,plain,
    ( X0_51 != k16_lattice3(sK5,X0_52)
    | k16_lattice3(sK5,X0_52) = X0_51
    | k16_lattice3(sK5,X0_52) != k16_lattice3(sK5,X0_52) ),
    inference(instantiation,[status(thm)],[c_4374])).

cnf(c_7758,plain,
    ( k16_lattice3(sK5,X0_52) != k16_lattice3(sK5,X0_52)
    | k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X1_52))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X1_52)) != k16_lattice3(sK5,X0_52) ),
    inference(instantiation,[status(thm)],[c_4888])).

cnf(c_7768,plain,
    ( k16_lattice3(sK5,sK7) != k16_lattice3(sK5,sK7)
    | k16_lattice3(sK5,sK7) = k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != k16_lattice3(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_7758])).

cnf(c_4077,plain,
    ( X0_51 != X1_51
    | X0_51 = k15_lattice3(sK5,X0_52)
    | k15_lattice3(sK5,X0_52) != X1_51 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_7711,plain,
    ( X0_51 != X1_51
    | X0_51 = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) != X1_51 ),
    inference(instantiation,[status(thm)],[c_4077])).

cnf(c_7712,plain,
    ( k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != sK6
    | sK6 = k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_7711])).

cnf(c_9,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_708,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r4_lattice3(X0,sK2(X0,X2,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_709,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_32,c_31,c_29])).

cnf(c_714,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_713])).

cnf(c_3016,plain,
    ( ~ r4_lattice3(sK5,X0_51,X0_52)
    | r4_lattice3(sK5,sK2(sK5,X0_52,X0_51),X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_714])).

cnf(c_6528,plain,
    ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),a_2_1_lattice3(sK5,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_6543,plain,
    ( r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),a_2_1_lattice3(sK5,sK7))
    | ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
    inference(instantiation,[status(thm)],[c_6528])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_732,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_733,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_32,c_31,c_29])).

cnf(c_738,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_3015,plain,
    ( ~ r4_lattice3(sK5,X0_51,X0_52)
    | ~ r1_lattices(sK5,X0_51,sK2(sK5,X0_52,X0_51))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_6529,plain,
    ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | ~ r1_lattices(sK5,X0_51,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_6539,plain,
    ( ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
    | ~ r1_lattices(sK5,sK6,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
    inference(instantiation,[status(thm)],[c_6529])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_684,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,X2) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_685,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_689,plain,
    ( m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r4_lattice3(sK5,X0,X1)
    | k15_lattice3(sK5,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_32,c_31,c_29])).

cnf(c_690,plain,
    ( ~ r4_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
    | k15_lattice3(sK5,X1) = X0 ),
    inference(renaming,[status(thm)],[c_689])).

cnf(c_3017,plain,
    ( ~ r4_lattice3(sK5,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,X0_52,X0_51),u1_struct_0(sK5))
    | k15_lattice3(sK5,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_690])).

cnf(c_6531,plain,
    ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
    | m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3017])).

cnf(c_6533,plain,
    ( ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
    | m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
    inference(instantiation,[status(thm)],[c_6531])).

cnf(c_5339,plain,
    ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5337])).

cnf(c_4437,plain,
    ( ~ r3_lattice3(sK5,X0_51,X0_52)
    | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52)
    | k15_lattice3(sK5,X1_52) != X0_51 ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_5155,plain,
    ( ~ r3_lattice3(sK5,X0_51,X0_52)
    | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52)
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) != X0_51 ),
    inference(instantiation,[status(thm)],[c_4437])).

cnf(c_5157,plain,
    ( r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),sK7)
    | ~ r3_lattice3(sK5,sK6,sK7)
    | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != sK6 ),
    inference(instantiation,[status(thm)],[c_5155])).

cnf(c_3983,plain,
    ( k16_lattice3(sK5,sK7) != X0_51
    | k16_lattice3(sK5,sK7) = sK6
    | sK6 != X0_51 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_4464,plain,
    ( k16_lattice3(sK5,sK7) != k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
    | k16_lattice3(sK5,sK7) = sK6
    | sK6 != k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_3983])).

cnf(c_4016,plain,
    ( k16_lattice3(sK5,sK7) = k16_lattice3(sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_3083,plain,
    ( ~ r3_lattice3(sK5,sK6,sK7)
    | r2_hidden(sK6,a_2_1_lattice3(sK5,sK7))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3013])).

cnf(c_25,negated_conjecture,
    ( k16_lattice3(sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3029,negated_conjecture,
    ( k16_lattice3(sK5,sK7) != sK6 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3046,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_26,negated_conjecture,
    ( r3_lattice3(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK6,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11697,c_9851,c_7840,c_7768,c_7712,c_6543,c_6539,c_6533,c_5339,c_5157,c_4464,c_4016,c_3083,c_3029,c_3046,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:18:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.98  
% 3.78/0.98  ------  iProver source info
% 3.78/0.98  
% 3.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.98  git: non_committed_changes: false
% 3.78/0.98  git: last_make_outside_of_git: false
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  ------ Parsing...
% 3.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  ------ Proving...
% 3.78/0.98  ------ Problem Properties 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  clauses                                 29
% 3.78/0.98  conjectures                             4
% 3.78/0.98  EPR                                     2
% 3.78/0.98  Horn                                    21
% 3.78/0.98  unary                                   6
% 3.78/0.98  binary                                  4
% 3.78/0.98  lits                                    82
% 3.78/0.98  lits eq                                 8
% 3.78/0.98  fd_pure                                 0
% 3.78/0.98  fd_pseudo                               0
% 3.78/0.98  fd_cond                                 0
% 3.78/0.98  fd_pseudo_cond                          6
% 3.78/0.98  AC symbols                              0
% 3.78/0.98  
% 3.78/0.98  ------ Input Options Time Limit: Unbounded
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  Current options:
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS status Theorem for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  fof(f5,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f18,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 3.78/0.98    inference(ennf_transformation,[],[f5])).
% 3.78/0.98  
% 3.78/0.98  fof(f19,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.78/0.98    inference(flattening,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f39,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.78/0.98    inference(nnf_transformation,[],[f19])).
% 3.78/0.98  
% 3.78/0.98  fof(f40,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.78/0.98    inference(rectify,[],[f39])).
% 3.78/0.98  
% 3.78/0.98  fof(f41,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f42,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK3(X0,X1,X2),X2) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 3.78/0.98  
% 3.78/0.98  fof(f67,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f42])).
% 3.78/0.98  
% 3.78/0.98  fof(f8,conjecture,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f9,negated_conjecture,(
% 3.78/0.98    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 3.78/0.98    inference(negated_conjecture,[],[f8])).
% 3.78/0.98  
% 3.78/0.98  fof(f24,plain,(
% 3.78/0.98    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f9])).
% 3.78/0.98  
% 3.78/0.98  fof(f25,plain,(
% 3.78/0.98    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f24])).
% 3.78/0.98  
% 3.78/0.98  fof(f50,plain,(
% 3.78/0.98    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK7) != X1 & r3_lattice3(X0,X1,sK7) & r2_hidden(X1,sK7))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f49,plain,(
% 3.78/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK6 & r3_lattice3(X0,sK6,X2) & r2_hidden(sK6,X2)) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f48,plain,(
% 3.78/0.98    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK5,X2) != X1 & r3_lattice3(sK5,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK5))) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f51,plain,(
% 3.78/0.98    ((k16_lattice3(sK5,sK7) != sK6 & r3_lattice3(sK5,sK6,sK7) & r2_hidden(sK6,sK7)) & m1_subset_1(sK6,u1_struct_0(sK5))) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f50,f49,f48])).
% 3.78/0.98  
% 3.78/0.98  fof(f80,plain,(
% 3.78/0.98    l3_lattices(sK5)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f77,plain,(
% 3.78/0.98    ~v2_struct_0(sK5)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f68,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK3(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f42])).
% 3.78/0.98  
% 3.78/0.98  fof(f2,axiom,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f12,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f2])).
% 3.78/0.98  
% 3.78/0.98  fof(f13,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f12])).
% 3.78/0.98  
% 3.78/0.98  fof(f30,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(nnf_transformation,[],[f13])).
% 3.78/0.98  
% 3.78/0.98  fof(f31,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(rectify,[],[f30])).
% 3.78/0.98  
% 3.78/0.98  fof(f32,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f33,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.78/0.98  
% 3.78/0.98  fof(f58,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f33])).
% 3.78/0.98  
% 3.78/0.98  fof(f1,axiom,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f10,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f1])).
% 3.78/0.98  
% 3.78/0.98  fof(f11,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f10])).
% 3.78/0.98  
% 3.78/0.98  fof(f26,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(nnf_transformation,[],[f11])).
% 3.78/0.98  
% 3.78/0.98  fof(f27,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(rectify,[],[f26])).
% 3.78/0.98  
% 3.78/0.98  fof(f28,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f29,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.78/0.98  
% 3.78/0.98  fof(f52,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f29])).
% 3.78/0.98  
% 3.78/0.98  fof(f66,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f42])).
% 3.78/0.98  
% 3.78/0.98  fof(f59,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f33])).
% 3.78/0.98  
% 3.78/0.98  fof(f6,axiom,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f20,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f6])).
% 3.78/0.98  
% 3.78/0.98  fof(f21,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f20])).
% 3.78/0.98  
% 3.78/0.98  fof(f43,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(nnf_transformation,[],[f21])).
% 3.78/0.98  
% 3.78/0.98  fof(f44,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f43])).
% 3.78/0.98  
% 3.78/0.98  fof(f45,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(rectify,[],[f44])).
% 3.78/0.98  
% 3.78/0.98  fof(f46,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK4(X0,X1,X2),X1) & r3_lattice3(X0,sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f47,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK4(X0,X1,X2),X1) & r3_lattice3(X0,sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 3.78/0.98  
% 3.78/0.98  fof(f73,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK4(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f47])).
% 3.78/0.98  
% 3.78/0.98  fof(f79,plain,(
% 3.78/0.98    v4_lattice3(sK5)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f78,plain,(
% 3.78/0.98    v10_lattices(sK5)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f72,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f47])).
% 3.78/0.98  
% 3.78/0.98  fof(f69,plain,(
% 3.78/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f42])).
% 3.78/0.98  
% 3.78/0.98  fof(f87,plain,(
% 3.78/0.98    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.78/0.98    inference(equality_resolution,[],[f69])).
% 3.78/0.98  
% 3.78/0.98  fof(f7,axiom,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f22,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f7])).
% 3.78/0.98  
% 3.78/0.98  fof(f23,plain,(
% 3.78/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f22])).
% 3.78/0.98  
% 3.78/0.98  fof(f75,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f23])).
% 3.78/0.98  
% 3.78/0.98  fof(f74,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK4(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f47])).
% 3.78/0.98  
% 3.78/0.98  fof(f4,axiom,(
% 3.78/0.98    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f16,plain,(
% 3.78/0.98    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f4])).
% 3.78/0.98  
% 3.78/0.98  fof(f17,plain,(
% 3.78/0.98    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f65,plain,(
% 3.78/0.98    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f17])).
% 3.78/0.98  
% 3.78/0.98  fof(f56,plain,(
% 3.78/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f33])).
% 3.78/0.98  
% 3.78/0.98  fof(f3,axiom,(
% 3.78/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f14,plain,(
% 3.78/0.98    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.78/0.98    inference(ennf_transformation,[],[f3])).
% 3.78/0.98  
% 3.78/0.98  fof(f15,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f14])).
% 3.78/0.98  
% 3.78/0.98  fof(f34,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(nnf_transformation,[],[f15])).
% 3.78/0.98  
% 3.78/0.98  fof(f35,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(flattening,[],[f34])).
% 3.78/0.98  
% 3.78/0.98  fof(f36,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(rectify,[],[f35])).
% 3.78/0.98  
% 3.78/0.98  fof(f37,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f38,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.78/0.98  
% 3.78/0.98  fof(f63,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK2(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  fof(f64,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK2(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  fof(f62,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  fof(f84,plain,(
% 3.78/0.98    k16_lattice3(sK5,sK7) != sK6),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f83,plain,(
% 3.78/0.98    r3_lattice3(sK5,sK6,sK7)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f82,plain,(
% 3.78/0.98    r2_hidden(sK6,sK7)),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  fof(f81,plain,(
% 3.78/0.98    m1_subset_1(sK6,u1_struct_0(sK5))),
% 3.78/0.98    inference(cnf_transformation,[],[f51])).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3032,plain,
% 3.78/0.98      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3031,plain,( X0_51 = X0_51 ),theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4210,plain,
% 3.78/0.98      ( X0_51 != X1_51 | X1_51 = X0_51 ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_3032,c_3031]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_16,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.78/0.98      | v2_struct_0(X1)
% 3.78/0.98      | ~ l3_lattices(X1)
% 3.78/0.98      | sK3(X0,X1,X2) = X0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_29,negated_conjecture,
% 3.78/0.98      ( l3_lattices(sK5) ),
% 3.78/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1141,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.78/0.98      | v2_struct_0(X1)
% 3.78/0.98      | sK3(X0,X1,X2) = X0
% 3.78/0.98      | sK5 != X1 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1142,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | sK3(X0,sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_1141]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_32,negated_conjecture,
% 3.78/0.98      ( ~ v2_struct_0(sK5) ),
% 3.78/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1146,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) | sK3(X0,sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_1142,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3002,plain,
% 3.78/0.98      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | sK3(X0_51,sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_1146]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4954,plain,
% 3.78/0.98      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | X0_51 = sK3(X0_51,sK5,X0_52) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_4210,c_3002]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3033,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0_50,X0_51,X0_52)
% 3.78/0.98      | r3_lattice3(X0_50,X1_51,X0_52)
% 3.78/0.98      | X1_51 != X0_51 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5388,plain,
% 3.78/0.98      ( r3_lattice3(X0_50,X0_51,X0_52)
% 3.78/0.98      | ~ r3_lattice3(X0_50,sK3(X0_51,sK5,X1_52),X0_52)
% 3.78/0.98      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X1_52)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_4954,c_3033]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15,plain,
% 3.78/0.98      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.78/0.98      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_889,plain,
% 3.78/0.98      ( r3_lattice3(X0,sK3(X1,X0,X2),X2)
% 3.78/0.98      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_890,plain,
% 3.78/0.98      ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
% 3.78/0.98      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_889]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_894,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | r3_lattice3(sK5,sK3(X0,sK5,X1),X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_890,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_895,plain,
% 3.78/0.98      ( r3_lattice3(sK5,sK3(X0,sK5,X1),X1)
% 3.78/0.98      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_894]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3014,plain,
% 3.78/0.98      ( r3_lattice3(sK5,sK3(X0_51,sK5,X0_52),X0_52)
% 3.78/0.98      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_895]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7071,plain,
% 3.78/0.98      ( r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_5388,c_3014]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5,plain,
% 3.78/0.98      ( r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_991,plain,
% 3.78/0.98      ( r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_992,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r2_hidden(sK1(sK5,X0,X1),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_991]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_996,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | r2_hidden(sK1(sK5,X0,X1),X1)
% 3.78/0.98      | r4_lattice3(sK5,X0,X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_992,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_997,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r2_hidden(sK1(sK5,X0,X1),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_996]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3009,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r2_hidden(sK1(sK5,X0_51,X0_52),X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_997]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7214,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | r3_lattice3(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_7071,c_3009]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3,plain,
% 3.78/0.98      ( r1_lattices(X0,X1,X2)
% 3.78/0.98      | ~ r3_lattice3(X0,X1,X3)
% 3.78/0.98      | ~ r2_hidden(X2,X3)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1033,plain,
% 3.78/0.98      ( r1_lattices(X0,X1,X2)
% 3.78/0.98      | ~ r3_lattice3(X0,X1,X3)
% 3.78/0.98      | ~ r2_hidden(X2,X3)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1034,plain,
% 3.78/0.98      ( r1_lattices(sK5,X0,X1)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X2)
% 3.78/0.98      | ~ r2_hidden(X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_1033]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1038,plain,
% 3.78/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r2_hidden(X1,X2)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X2)
% 3.78/0.98      | r1_lattices(sK5,X0,X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_1034,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1039,plain,
% 3.78/0.98      ( r1_lattices(sK5,X0,X1)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X2)
% 3.78/0.98      | ~ r2_hidden(X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_1038]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3007,plain,
% 3.78/0.98      ( r1_lattices(sK5,X0_51,X1_51)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ r2_hidden(X1_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_1039]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7308,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
% 3.78/0.98      | ~ r2_hidden(X1_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_7214,c_3007]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3035,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0_51,X0_53)
% 3.78/0.98      | m1_subset_1(X1_51,X0_53)
% 3.78/0.98      | X1_51 != X0_51 ),
% 3.78/0.98      theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5386,plain,
% 3.78/0.98      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | m1_subset_1(X0_51,X0_53)
% 3.78/0.98      | ~ m1_subset_1(sK3(X0_51,sK5,X0_52),X0_53) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_4954,c_3035]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_17,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.78/0.98      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 3.78/0.98      | v2_struct_0(X1)
% 3.78/0.98      | ~ l3_lattices(X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1123,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 3.78/0.98      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
% 3.78/0.98      | v2_struct_0(X1)
% 3.78/0.98      | sK5 != X1 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1124,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_1123]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1128,plain,
% 3.78/0.98      ( m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5))
% 3.78/0.98      | ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1)) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_1124,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1129,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | m1_subset_1(sK3(X0,sK5,X1),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_1128]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3003,plain,
% 3.78/0.98      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | m1_subset_1(sK3(X0_51,sK5,X0_52),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_1129]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6935,plain,
% 3.78/0.98      ( ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_5386,c_3003]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7094,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_6935,c_3009]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_11661,plain,
% 3.78/0.98      ( ~ m1_subset_1(X1_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ r2_hidden(X1_51,X0_52)
% 3.78/0.98      | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
% 3.78/0.98      | r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_7308,c_7094]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_11662,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | r1_lattices(sK5,sK1(sK5,X0_51,a_2_1_lattice3(sK5,X0_52)),X1_51)
% 3.78/0.98      | ~ r2_hidden(X1_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_11661]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4,plain,
% 3.78/0.98      ( r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1012,plain,
% 3.78/0.98      ( r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1013,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_1012]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1017,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 3.78/0.98      | r4_lattice3(sK5,X0,X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_1013,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1018,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ r1_lattices(sK5,sK1(sK5,X0,X1),X0)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_1017]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3008,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ r1_lattices(sK5,sK1(sK5,X0_51,X0_52),X0_51)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_1018]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_11695,plain,
% 3.78/0.98      ( r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ r2_hidden(X0_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(resolution,[status(thm)],[c_11662,c_3008]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_11697,plain,
% 3.78/0.98      ( r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ r2_hidden(sK6,sK7)
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_11695]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_19,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | r3_lattice3(X0,sK4(X0,X1,X2),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_30,negated_conjecture,
% 3.78/0.98      ( v4_lattice3(sK5) ),
% 3.78/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_612,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | r3_lattice3(X0,sK4(X0,X1,X2),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_613,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_612]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_31,negated_conjecture,
% 3.78/0.98      ( v10_lattices(sK5) ),
% 3.78/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_617,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_613,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_618,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,X0,X1),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_617]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3019,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,X0_51,X0_52),X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_618]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3608,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) = X0_51
% 3.78/0.98      | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,X0_51,X0_52),X0_52) = iProver_top
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_20,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_588,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_589,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_588]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_593,plain,
% 3.78/0.98      ( m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_589,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_594,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_593]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3020,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK4(sK5,X0_51,X0_52),u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_594]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3607,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) = X0_51
% 3.78/0.98      | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top
% 3.78/0.98      | m1_subset_1(sK4(sK5,X0_51,X0_52),u1_struct_0(sK5)) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3020]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_14,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_907,plain,
% 3.78/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_908,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_907]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_912,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_908,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_913,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | r2_hidden(X0,a_2_1_lattice3(sK5,X1))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_912]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3013,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_913]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3614,plain,
% 3.78/0.98      ( r3_lattice3(sK5,X0_51,X0_52) != iProver_top
% 3.78/0.98      | r2_hidden(X0_51,a_2_1_lattice3(sK5,X0_52)) = iProver_top
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3013]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_24,plain,
% 3.78/0.98      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.78/0.98      | ~ r2_hidden(X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_504,plain,
% 3.78/0.98      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.78/0.98      | ~ r2_hidden(X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_505,plain,
% 3.78/0.98      ( r3_lattices(sK5,X0,k15_lattice3(sK5,X1))
% 3.78/0.98      | ~ r2_hidden(X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_504]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_509,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r2_hidden(X0,X1)
% 3.78/0.98      | r3_lattices(sK5,X0,k15_lattice3(sK5,X1)) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_505,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_510,plain,
% 3.78/0.98      ( r3_lattices(sK5,X0,k15_lattice3(sK5,X1))
% 3.78/0.98      | ~ r2_hidden(X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_509]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3024,plain,
% 3.78/0.98      ( r3_lattices(sK5,X0_51,k15_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ r2_hidden(X0_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_510]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3603,plain,
% 3.78/0.98      ( r3_lattices(sK5,X0_51,k15_lattice3(sK5,X0_52)) = iProver_top
% 3.78/0.98      | r2_hidden(X0_51,X0_52) != iProver_top
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3024]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_18,plain,
% 3.78/0.98      ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
% 3.78/0.98      | ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_636,plain,
% 3.78/0.98      ( ~ r3_lattices(X0,sK4(X0,X1,X2),X1)
% 3.78/0.98      | ~ r3_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k16_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_637,plain,
% 3.78/0.98      ( ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_636]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_641,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_637,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_642,plain,
% 3.78/0.98      ( ~ r3_lattices(sK5,sK4(sK5,X0,X1),X0)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_641]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3018,plain,
% 3.78/0.98      ( ~ r3_lattices(sK5,sK4(sK5,X0_51,X0_52),X0_51)
% 3.78/0.98      | ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_642]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3609,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) = X0_51
% 3.78/0.98      | r3_lattices(sK5,sK4(sK5,X0_51,X0_52),X0_51) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,X0_51,X0_52) != iProver_top
% 3.78/0.98      | m1_subset_1(X0_51,u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3018]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4389,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,X1_52)
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52) != iProver_top
% 3.78/0.98      | r2_hidden(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),X1_52) != iProver_top
% 3.78/0.98      | m1_subset_1(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),u1_struct_0(sK5)) != iProver_top
% 3.78/0.98      | m1_subset_1(k15_lattice3(sK5,X1_52),u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3603,c_3609]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_13,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_928,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_929,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_928]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_933,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,X0),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_929,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3012,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,X0_52),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_933]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3615,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,X0_52),u1_struct_0(sK5)) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_3012]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6768,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,X1_52)
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52) != iProver_top
% 3.78/0.98      | r2_hidden(sK4(sK5,k15_lattice3(sK5,X1_52),X0_52),X1_52) != iProver_top ),
% 3.78/0.98      inference(forward_subsumption_resolution,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_4389,c_3615,c_3607]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6772,plain,
% 3.78/0.98      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
% 3.78/0.98      | m1_subset_1(sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3614,c_6768]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9834,plain,
% 3.78/0.98      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
% 3.78/0.98      | m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3607,c_6772]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5337,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3012]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5338,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_5337]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9839,plain,
% 3.78/0.98      ( r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_9834,c_5338]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9840,plain,
% 3.78/0.98      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X1_52)
% 3.78/0.98      | r3_lattice3(sK5,sK4(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52),X0_52) != iProver_top
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X1_52) != iProver_top ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_9839]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9848,plain,
% 3.78/0.98      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X0_52)
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52) != iProver_top
% 3.78/0.98      | m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5)) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3608,c_9840]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9849,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52)
% 3.78/0.98      | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = k16_lattice3(sK5,X0_52) ),
% 3.78/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_9848]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9851,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),sK7)
% 3.78/0.98      | ~ m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = k16_lattice3(sK5,sK7) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_9849]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r1_lattices(X0,X3,X1)
% 3.78/0.98      | ~ r2_hidden(X3,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0) ),
% 3.78/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_943,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r1_lattices(X0,X3,X1)
% 3.78/0.98      | ~ r2_hidden(X3,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_944,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r1_lattices(sK5,X2,X0)
% 3.78/0.98      | ~ r2_hidden(X2,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.78/0.98      | v2_struct_0(sK5) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_943]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_948,plain,
% 3.78/0.98      ( ~ m1_subset_1(X2,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r2_hidden(X2,X1)
% 3.78/0.98      | r1_lattices(sK5,X2,X0)
% 3.78/0.98      | ~ r4_lattice3(sK5,X0,X1) ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_944,c_32]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_949,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r1_lattices(sK5,X2,X0)
% 3.78/0.98      | ~ r2_hidden(X2,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_948]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3011,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r1_lattices(sK5,X1_51,X0_51)
% 3.78/0.98      | ~ r2_hidden(X1_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_949]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6530,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | r1_lattices(sK5,X1_51,X0_51)
% 3.78/0.98      | ~ r2_hidden(X1_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X1_51,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3011]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7838,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),a_2_1_lattice3(sK5,X1_52))
% 3.78/0.98      | r1_lattices(sK5,X0_51,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51))
% 3.78/0.98      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK5,X1_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_6530]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7840,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | r1_lattices(sK5,sK6,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6))
% 3.78/0.98      | ~ r2_hidden(sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_7838]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4374,plain,
% 3.78/0.98      ( X0_51 != X1_51
% 3.78/0.98      | k16_lattice3(sK5,X0_52) != X1_51
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3032]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4888,plain,
% 3.78/0.98      ( X0_51 != k16_lattice3(sK5,X0_52)
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = X0_51
% 3.78/0.98      | k16_lattice3(sK5,X0_52) != k16_lattice3(sK5,X0_52) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4374]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7758,plain,
% 3.78/0.98      ( k16_lattice3(sK5,X0_52) != k16_lattice3(sK5,X0_52)
% 3.78/0.98      | k16_lattice3(sK5,X0_52) = k15_lattice3(sK5,a_2_1_lattice3(sK5,X1_52))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X1_52)) != k16_lattice3(sK5,X0_52) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4888]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7768,plain,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) != k16_lattice3(sK5,sK7)
% 3.78/0.98      | k16_lattice3(sK5,sK7) = k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != k16_lattice3(sK5,sK7) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_7758]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4077,plain,
% 3.78/0.98      ( X0_51 != X1_51
% 3.78/0.98      | X0_51 = k15_lattice3(sK5,X0_52)
% 3.78/0.98      | k15_lattice3(sK5,X0_52) != X1_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3032]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7711,plain,
% 3.78/0.98      ( X0_51 != X1_51
% 3.78/0.98      | X0_51 = k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) != X1_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4077]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_7712,plain,
% 3.78/0.98      ( k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != sK6
% 3.78/0.98      | sK6 = k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | sK6 != sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_7711]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_9,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_708,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | r4_lattice3(X0,sK2(X0,X2,X1),X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_709,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_708]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_713,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 3.78/0.98      | ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_709,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_714,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | r4_lattice3(sK5,sK2(sK5,X1,X0),X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_713]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3016,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r4_lattice3(sK5,sK2(sK5,X0_52,X0_51),X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_714]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6528,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3016]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6543,plain,
% 3.78/0.98      ( r4_lattice3(sK5,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_6528]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_8,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_732,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ r1_lattices(X0,X1,sK2(X0,X2,X1))
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_733,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_732]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_737,plain,
% 3.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 3.78/0.98      | ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_733,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_738,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ r1_lattices(sK5,X0,sK2(sK5,X1,X0))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_737]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3015,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ r1_lattices(sK5,X0_51,sK2(sK5,X0_52,X0_51))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_738]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6529,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ r1_lattices(sK5,X0_51,sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3015]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6539,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ r1_lattices(sK5,sK6,sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6))
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_6529]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | ~ v4_lattice3(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_684,plain,
% 3.78/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.78/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/0.98      | m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
% 3.78/0.98      | ~ v10_lattices(X0)
% 3.78/0.98      | v2_struct_0(X0)
% 3.78/0.98      | ~ l3_lattices(X0)
% 3.78/0.98      | k15_lattice3(X0,X2) = X1
% 3.78/0.98      | sK5 != X0 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_685,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 3.78/0.98      | ~ v10_lattices(sK5)
% 3.78/0.98      | v2_struct_0(sK5)
% 3.78/0.98      | ~ l3_lattices(sK5)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_684]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_689,plain,
% 3.78/0.98      ( m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(global_propositional_subsumption,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_685,c_32,c_31,c_29]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_690,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0,X1)
% 3.78/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK2(sK5,X1,X0),u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X1) = X0 ),
% 3.78/0.98      inference(renaming,[status(thm)],[c_689]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3017,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK2(sK5,X0_52,X0_51),u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,X0_52) = X0_51 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_690]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6531,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,X0_51,a_2_1_lattice3(sK5,X0_52))
% 3.78/0.98      | ~ m1_subset_1(X0_51,u1_struct_0(sK5))
% 3.78/0.98      | m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,X0_52),X0_51),u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) = X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3017]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6533,plain,
% 3.78/0.98      ( ~ r4_lattice3(sK5,sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | m1_subset_1(sK2(sK5,a_2_1_lattice3(sK5,sK7),sK6),u1_struct_0(sK5))
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) = sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_6531]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5339,plain,
% 3.78/0.98      ( m1_subset_1(k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5337]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4437,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,X1_52),X0_52)
% 3.78/0.98      | k15_lattice3(sK5,X1_52) != X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3033]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5155,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,X0_51,X0_52)
% 3.78/0.98      | r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)),X0_52)
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,X0_52)) != X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4437]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5157,plain,
% 3.78/0.98      ( r3_lattice3(sK5,k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)),sK7)
% 3.78/0.98      | ~ r3_lattice3(sK5,sK6,sK7)
% 3.78/0.98      | k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) != sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5155]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3983,plain,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) != X0_51
% 3.78/0.98      | k16_lattice3(sK5,sK7) = sK6
% 3.78/0.98      | sK6 != X0_51 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3032]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4464,plain,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) != k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | k16_lattice3(sK5,sK7) = sK6
% 3.78/0.98      | sK6 != k15_lattice3(sK5,a_2_1_lattice3(sK5,sK7)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3983]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4016,plain,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) = k16_lattice3(sK5,sK7) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3031]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3083,plain,
% 3.78/0.98      ( ~ r3_lattice3(sK5,sK6,sK7)
% 3.78/0.98      | r2_hidden(sK6,a_2_1_lattice3(sK5,sK7))
% 3.78/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3013]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_25,negated_conjecture,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) != sK6 ),
% 3.78/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3029,negated_conjecture,
% 3.78/0.98      ( k16_lattice3(sK5,sK7) != sK6 ),
% 3.78/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3046,plain,
% 3.78/0.98      ( sK6 = sK6 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3031]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_26,negated_conjecture,
% 3.78/0.98      ( r3_lattice3(sK5,sK6,sK7) ),
% 3.78/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_27,negated_conjecture,
% 3.78/0.98      ( r2_hidden(sK6,sK7) ),
% 3.78/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_28,negated_conjecture,
% 3.78/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(contradiction,plain,
% 3.78/0.98      ( $false ),
% 3.78/0.98      inference(minisat,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_11697,c_9851,c_7840,c_7768,c_7712,c_6543,c_6539,
% 3.78/0.98                 c_6533,c_5339,c_5157,c_4464,c_4016,c_3083,c_3029,c_3046,
% 3.78/0.98                 c_26,c_27,c_28]) ).
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  ------                               Statistics
% 3.78/0.98  
% 3.78/0.98  ------ Selected
% 3.78/0.98  
% 3.78/0.98  total_time:                             0.337
% 3.78/0.98  
%------------------------------------------------------------------------------
