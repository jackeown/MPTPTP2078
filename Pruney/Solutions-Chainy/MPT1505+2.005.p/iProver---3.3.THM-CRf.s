%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:10 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 470 expanded)
%              Number of clauses        :   66 ( 105 expanded)
%              Number of leaves         :   16 ( 136 expanded)
%              Depth                    :   16
%              Number of atoms          :  835 (3237 expanded)
%              Number of equality atoms :   42 (  44 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
            | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
          & r2_hidden(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK6),X1)
          | ~ r3_lattices(X0,X1,k15_lattice3(X0,sK6)) )
        & r2_hidden(X1,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),sK5)
              | ~ r3_lattices(X0,sK5,k15_lattice3(X0,X2)) )
            & r2_hidden(sK5,X2) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
              ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,X2),X1)
                | ~ r3_lattices(sK4,X1,k15_lattice3(sK4,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) )
    & r2_hidden(sK5,sK6)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f53,f52,f51])).

fof(f81,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
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

fof(f56,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1040,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_1041,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_29])).

cnf(c_1046,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1045])).

cnf(c_2494,plain,
    ( ~ r4_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X1_53,X0_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1046])).

cnf(c_3613,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),X0_54)
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,X0_54)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_3615,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3613])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_397,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_401,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_2,c_1])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_967,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_31])).

cnf(c_968,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_972,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_32,c_29])).

cnf(c_973,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_972])).

cnf(c_2497,plain,
    ( ~ r1_lattices(sK4,X0_53,X1_53)
    | r3_lattices(sK4,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_973])).

cnf(c_3422,plain,
    ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1130,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_1131,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1130])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1131,c_29])).

cnf(c_1136,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1135])).

cnf(c_2490,plain,
    ( ~ r3_lattice3(sK4,X0_53,X0_54)
    | r1_lattices(sK4,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1136])).

cnf(c_3301,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54)
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r2_hidden(sK5,X0_54)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_3306,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6)
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3301])).

cnf(c_25,plain,
    ( ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_700,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_701,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_705,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_32,c_31,c_29])).

cnf(c_2506,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) = k15_lattice3(sK4,X0_54) ),
    inference(subtyping,[status(esa)],[c_705])).

cnf(c_19,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1025,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_1026,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_1030,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_29])).

cnf(c_2495,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1030])).

cnf(c_3003,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2495])).

cnf(c_3287,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_3003])).

cnf(c_3288,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3287])).

cnf(c_3290,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3288])).

cnf(c_3228,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_2566,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2495])).

cnf(c_18,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_807,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_808,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_812,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_32,c_31,c_29])).

cnf(c_813,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_812])).

cnf(c_2502,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
    | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_813])).

cnf(c_2545,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_24,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_191,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_19])).

cnf(c_685,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_30])).

cnf(c_686,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_690,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_32,c_31,c_29])).

cnf(c_2507,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_690])).

cnf(c_2532,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2507])).

cnf(c_26,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3615,c_3422,c_3306,c_3290,c_3228,c_2566,c_2545,c_2532,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:35:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.89/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/0.99  
% 1.89/0.99  ------  iProver source info
% 1.89/0.99  
% 1.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/0.99  git: non_committed_changes: false
% 1.89/0.99  git: last_make_outside_of_git: false
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     num_symb
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       true
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  ------ Parsing...
% 1.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/0.99  ------ Proving...
% 1.89/0.99  ------ Problem Properties 
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  clauses                                 25
% 1.89/0.99  conjectures                             3
% 1.89/0.99  EPR                                     1
% 1.89/0.99  Horn                                    17
% 1.89/0.99  unary                                   5
% 1.89/0.99  binary                                  2
% 1.89/0.99  lits                                    76
% 1.89/0.99  lits eq                                 7
% 1.89/0.99  fd_pure                                 0
% 1.89/0.99  fd_pseudo                               0
% 1.89/0.99  fd_cond                                 0
% 1.89/0.99  fd_pseudo_cond                          6
% 1.89/0.99  AC symbols                              0
% 1.89/0.99  
% 1.89/0.99  ------ Schedule dynamic 5 is on 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ 
% 1.89/0.99  Current options:
% 1.89/0.99  ------ 
% 1.89/0.99  
% 1.89/0.99  ------ Input Options
% 1.89/0.99  
% 1.89/0.99  --out_options                           all
% 1.89/0.99  --tptp_safe_out                         true
% 1.89/0.99  --problem_path                          ""
% 1.89/0.99  --include_path                          ""
% 1.89/0.99  --clausifier                            res/vclausify_rel
% 1.89/0.99  --clausifier_options                    --mode clausify
% 1.89/0.99  --stdin                                 false
% 1.89/0.99  --stats_out                             all
% 1.89/0.99  
% 1.89/0.99  ------ General Options
% 1.89/0.99  
% 1.89/0.99  --fof                                   false
% 1.89/0.99  --time_out_real                         305.
% 1.89/0.99  --time_out_virtual                      -1.
% 1.89/0.99  --symbol_type_check                     false
% 1.89/0.99  --clausify_out                          false
% 1.89/0.99  --sig_cnt_out                           false
% 1.89/0.99  --trig_cnt_out                          false
% 1.89/0.99  --trig_cnt_out_tolerance                1.
% 1.89/0.99  --trig_cnt_out_sk_spl                   false
% 1.89/0.99  --abstr_cl_out                          false
% 1.89/0.99  
% 1.89/0.99  ------ Global Options
% 1.89/0.99  
% 1.89/0.99  --schedule                              default
% 1.89/0.99  --add_important_lit                     false
% 1.89/0.99  --prop_solver_per_cl                    1000
% 1.89/0.99  --min_unsat_core                        false
% 1.89/0.99  --soft_assumptions                      false
% 1.89/0.99  --soft_lemma_size                       3
% 1.89/0.99  --prop_impl_unit_size                   0
% 1.89/0.99  --prop_impl_unit                        []
% 1.89/0.99  --share_sel_clauses                     true
% 1.89/0.99  --reset_solvers                         false
% 1.89/0.99  --bc_imp_inh                            [conj_cone]
% 1.89/0.99  --conj_cone_tolerance                   3.
% 1.89/0.99  --extra_neg_conj                        none
% 1.89/0.99  --large_theory_mode                     true
% 1.89/0.99  --prolific_symb_bound                   200
% 1.89/0.99  --lt_threshold                          2000
% 1.89/0.99  --clause_weak_htbl                      true
% 1.89/0.99  --gc_record_bc_elim                     false
% 1.89/0.99  
% 1.89/0.99  ------ Preprocessing Options
% 1.89/0.99  
% 1.89/0.99  --preprocessing_flag                    true
% 1.89/0.99  --time_out_prep_mult                    0.1
% 1.89/0.99  --splitting_mode                        input
% 1.89/0.99  --splitting_grd                         true
% 1.89/0.99  --splitting_cvd                         false
% 1.89/0.99  --splitting_cvd_svl                     false
% 1.89/0.99  --splitting_nvd                         32
% 1.89/0.99  --sub_typing                            true
% 1.89/0.99  --prep_gs_sim                           true
% 1.89/0.99  --prep_unflatten                        true
% 1.89/0.99  --prep_res_sim                          true
% 1.89/0.99  --prep_upred                            true
% 1.89/0.99  --prep_sem_filter                       exhaustive
% 1.89/0.99  --prep_sem_filter_out                   false
% 1.89/0.99  --pred_elim                             true
% 1.89/0.99  --res_sim_input                         true
% 1.89/0.99  --eq_ax_congr_red                       true
% 1.89/0.99  --pure_diseq_elim                       true
% 1.89/0.99  --brand_transform                       false
% 1.89/0.99  --non_eq_to_eq                          false
% 1.89/0.99  --prep_def_merge                        true
% 1.89/0.99  --prep_def_merge_prop_impl              false
% 1.89/0.99  --prep_def_merge_mbd                    true
% 1.89/0.99  --prep_def_merge_tr_red                 false
% 1.89/0.99  --prep_def_merge_tr_cl                  false
% 1.89/0.99  --smt_preprocessing                     true
% 1.89/0.99  --smt_ac_axioms                         fast
% 1.89/0.99  --preprocessed_out                      false
% 1.89/0.99  --preprocessed_stats                    false
% 1.89/0.99  
% 1.89/0.99  ------ Abstraction refinement Options
% 1.89/0.99  
% 1.89/0.99  --abstr_ref                             []
% 1.89/0.99  --abstr_ref_prep                        false
% 1.89/0.99  --abstr_ref_until_sat                   false
% 1.89/0.99  --abstr_ref_sig_restrict                funpre
% 1.89/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.99  --abstr_ref_under                       []
% 1.89/0.99  
% 1.89/0.99  ------ SAT Options
% 1.89/0.99  
% 1.89/0.99  --sat_mode                              false
% 1.89/0.99  --sat_fm_restart_options                ""
% 1.89/0.99  --sat_gr_def                            false
% 1.89/0.99  --sat_epr_types                         true
% 1.89/0.99  --sat_non_cyclic_types                  false
% 1.89/0.99  --sat_finite_models                     false
% 1.89/0.99  --sat_fm_lemmas                         false
% 1.89/0.99  --sat_fm_prep                           false
% 1.89/0.99  --sat_fm_uc_incr                        true
% 1.89/0.99  --sat_out_model                         small
% 1.89/0.99  --sat_out_clauses                       false
% 1.89/0.99  
% 1.89/0.99  ------ QBF Options
% 1.89/0.99  
% 1.89/0.99  --qbf_mode                              false
% 1.89/0.99  --qbf_elim_univ                         false
% 1.89/0.99  --qbf_dom_inst                          none
% 1.89/0.99  --qbf_dom_pre_inst                      false
% 1.89/0.99  --qbf_sk_in                             false
% 1.89/0.99  --qbf_pred_elim                         true
% 1.89/0.99  --qbf_split                             512
% 1.89/0.99  
% 1.89/0.99  ------ BMC1 Options
% 1.89/0.99  
% 1.89/0.99  --bmc1_incremental                      false
% 1.89/0.99  --bmc1_axioms                           reachable_all
% 1.89/0.99  --bmc1_min_bound                        0
% 1.89/0.99  --bmc1_max_bound                        -1
% 1.89/0.99  --bmc1_max_bound_default                -1
% 1.89/0.99  --bmc1_symbol_reachability              true
% 1.89/0.99  --bmc1_property_lemmas                  false
% 1.89/0.99  --bmc1_k_induction                      false
% 1.89/0.99  --bmc1_non_equiv_states                 false
% 1.89/0.99  --bmc1_deadlock                         false
% 1.89/0.99  --bmc1_ucm                              false
% 1.89/0.99  --bmc1_add_unsat_core                   none
% 1.89/0.99  --bmc1_unsat_core_children              false
% 1.89/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.99  --bmc1_out_stat                         full
% 1.89/0.99  --bmc1_ground_init                      false
% 1.89/0.99  --bmc1_pre_inst_next_state              false
% 1.89/0.99  --bmc1_pre_inst_state                   false
% 1.89/0.99  --bmc1_pre_inst_reach_state             false
% 1.89/0.99  --bmc1_out_unsat_core                   false
% 1.89/0.99  --bmc1_aig_witness_out                  false
% 1.89/0.99  --bmc1_verbose                          false
% 1.89/0.99  --bmc1_dump_clauses_tptp                false
% 1.89/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.99  --bmc1_dump_file                        -
% 1.89/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.99  --bmc1_ucm_extend_mode                  1
% 1.89/0.99  --bmc1_ucm_init_mode                    2
% 1.89/0.99  --bmc1_ucm_cone_mode                    none
% 1.89/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.99  --bmc1_ucm_relax_model                  4
% 1.89/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.99  --bmc1_ucm_layered_model                none
% 1.89/0.99  --bmc1_ucm_max_lemma_size               10
% 1.89/0.99  
% 1.89/0.99  ------ AIG Options
% 1.89/0.99  
% 1.89/0.99  --aig_mode                              false
% 1.89/0.99  
% 1.89/0.99  ------ Instantiation Options
% 1.89/0.99  
% 1.89/0.99  --instantiation_flag                    true
% 1.89/0.99  --inst_sos_flag                         false
% 1.89/0.99  --inst_sos_phase                        true
% 1.89/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.99  --inst_lit_sel_side                     none
% 1.89/0.99  --inst_solver_per_active                1400
% 1.89/0.99  --inst_solver_calls_frac                1.
% 1.89/0.99  --inst_passive_queue_type               priority_queues
% 1.89/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.99  --inst_passive_queues_freq              [25;2]
% 1.89/0.99  --inst_dismatching                      true
% 1.89/0.99  --inst_eager_unprocessed_to_passive     true
% 1.89/0.99  --inst_prop_sim_given                   true
% 1.89/0.99  --inst_prop_sim_new                     false
% 1.89/0.99  --inst_subs_new                         false
% 1.89/0.99  --inst_eq_res_simp                      false
% 1.89/0.99  --inst_subs_given                       false
% 1.89/0.99  --inst_orphan_elimination               true
% 1.89/0.99  --inst_learning_loop_flag               true
% 1.89/0.99  --inst_learning_start                   3000
% 1.89/0.99  --inst_learning_factor                  2
% 1.89/0.99  --inst_start_prop_sim_after_learn       3
% 1.89/0.99  --inst_sel_renew                        solver
% 1.89/0.99  --inst_lit_activity_flag                true
% 1.89/0.99  --inst_restr_to_given                   false
% 1.89/0.99  --inst_activity_threshold               500
% 1.89/0.99  --inst_out_proof                        true
% 1.89/0.99  
% 1.89/0.99  ------ Resolution Options
% 1.89/0.99  
% 1.89/0.99  --resolution_flag                       false
% 1.89/0.99  --res_lit_sel                           adaptive
% 1.89/0.99  --res_lit_sel_side                      none
% 1.89/0.99  --res_ordering                          kbo
% 1.89/0.99  --res_to_prop_solver                    active
% 1.89/0.99  --res_prop_simpl_new                    false
% 1.89/0.99  --res_prop_simpl_given                  true
% 1.89/0.99  --res_passive_queue_type                priority_queues
% 1.89/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.99  --res_passive_queues_freq               [15;5]
% 1.89/0.99  --res_forward_subs                      full
% 1.89/0.99  --res_backward_subs                     full
% 1.89/0.99  --res_forward_subs_resolution           true
% 1.89/0.99  --res_backward_subs_resolution          true
% 1.89/0.99  --res_orphan_elimination                true
% 1.89/0.99  --res_time_limit                        2.
% 1.89/0.99  --res_out_proof                         true
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Options
% 1.89/0.99  
% 1.89/0.99  --superposition_flag                    true
% 1.89/0.99  --sup_passive_queue_type                priority_queues
% 1.89/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.99  --demod_completeness_check              fast
% 1.89/0.99  --demod_use_ground                      true
% 1.89/0.99  --sup_to_prop_solver                    passive
% 1.89/0.99  --sup_prop_simpl_new                    true
% 1.89/0.99  --sup_prop_simpl_given                  true
% 1.89/0.99  --sup_fun_splitting                     false
% 1.89/0.99  --sup_smt_interval                      50000
% 1.89/0.99  
% 1.89/0.99  ------ Superposition Simplification Setup
% 1.89/0.99  
% 1.89/0.99  --sup_indices_passive                   []
% 1.89/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_full_bw                           [BwDemod]
% 1.89/0.99  --sup_immed_triv                        [TrivRules]
% 1.89/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_immed_bw_main                     []
% 1.89/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.99  
% 1.89/0.99  ------ Combination Options
% 1.89/0.99  
% 1.89/0.99  --comb_res_mult                         3
% 1.89/0.99  --comb_sup_mult                         2
% 1.89/0.99  --comb_inst_mult                        10
% 1.89/0.99  
% 1.89/0.99  ------ Debug Options
% 1.89/0.99  
% 1.89/0.99  --dbg_backtrace                         false
% 1.89/0.99  --dbg_dump_prop_clauses                 false
% 1.89/0.99  --dbg_dump_prop_clauses_file            -
% 1.89/0.99  --dbg_out_stat                          false
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  ------ Proving...
% 1.89/0.99  
% 1.89/0.99  
% 1.89/0.99  % SZS status Theorem for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/0.99  
% 1.89/0.99  fof(f4,axiom,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f20,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f4])).
% 1.89/0.99  
% 1.89/0.99  fof(f21,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f20])).
% 1.89/0.99  
% 1.89/0.99  fof(f37,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f21])).
% 1.89/0.99  
% 1.89/0.99  fof(f38,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(rectify,[],[f37])).
% 1.89/0.99  
% 1.89/0.99  fof(f39,plain,(
% 1.89/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f40,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 1.89/0.99  
% 1.89/0.99  fof(f65,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f40])).
% 1.89/0.99  
% 1.89/0.99  fof(f9,conjecture,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f10,negated_conjecture,(
% 1.89/0.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.89/0.99    inference(negated_conjecture,[],[f9])).
% 1.89/0.99  
% 1.89/0.99  fof(f30,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f10])).
% 1.89/0.99  
% 1.89/0.99  fof(f31,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f30])).
% 1.89/0.99  
% 1.89/0.99  fof(f53,plain,(
% 1.89/0.99    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,sK6))) & r2_hidden(X1,sK6))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f52,plain,(
% 1.89/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),sK5) | ~r3_lattices(X0,sK5,k15_lattice3(X0,X2))) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f51,plain,(
% 1.89/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),X1) | ~r3_lattices(sK4,X1,k15_lattice3(sK4,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f54,plain,(
% 1.89/0.99    (((~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f53,f52,f51])).
% 1.89/0.99  
% 1.89/0.99  fof(f81,plain,(
% 1.89/0.99    ~v2_struct_0(sK4)),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f84,plain,(
% 1.89/0.99    l3_lattices(sK4)),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f1,axiom,(
% 1.89/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f11,plain,(
% 1.89/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.89/0.99    inference(pure_predicate_removal,[],[f1])).
% 1.89/0.99  
% 1.89/0.99  fof(f12,plain,(
% 1.89/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.89/0.99    inference(pure_predicate_removal,[],[f11])).
% 1.89/0.99  
% 1.89/0.99  fof(f13,plain,(
% 1.89/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.89/0.99    inference(pure_predicate_removal,[],[f12])).
% 1.89/0.99  
% 1.89/0.99  fof(f14,plain,(
% 1.89/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.89/0.99    inference(ennf_transformation,[],[f13])).
% 1.89/0.99  
% 1.89/0.99  fof(f15,plain,(
% 1.89/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.89/0.99    inference(flattening,[],[f14])).
% 1.89/0.99  
% 1.89/0.99  fof(f58,plain,(
% 1.89/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f15])).
% 1.89/0.99  
% 1.89/0.99  fof(f2,axiom,(
% 1.89/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f16,plain,(
% 1.89/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f2])).
% 1.89/0.99  
% 1.89/0.99  fof(f17,plain,(
% 1.89/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f16])).
% 1.89/0.99  
% 1.89/0.99  fof(f32,plain,(
% 1.89/0.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f17])).
% 1.89/0.99  
% 1.89/0.99  fof(f60,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f32])).
% 1.89/0.99  
% 1.89/0.99  fof(f56,plain,(
% 1.89/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f15])).
% 1.89/0.99  
% 1.89/0.99  fof(f57,plain,(
% 1.89/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f15])).
% 1.89/0.99  
% 1.89/0.99  fof(f82,plain,(
% 1.89/0.99    v10_lattices(sK4)),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f3,axiom,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f18,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f3])).
% 1.89/0.99  
% 1.89/0.99  fof(f19,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f18])).
% 1.89/0.99  
% 1.89/0.99  fof(f33,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f19])).
% 1.89/0.99  
% 1.89/0.99  fof(f34,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(rectify,[],[f33])).
% 1.89/0.99  
% 1.89/0.99  fof(f35,plain,(
% 1.89/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f36,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 1.89/0.99  
% 1.89/0.99  fof(f61,plain,(
% 1.89/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f36])).
% 1.89/0.99  
% 1.89/0.99  fof(f8,axiom,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f28,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f8])).
% 1.89/0.99  
% 1.89/0.99  fof(f29,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f28])).
% 1.89/0.99  
% 1.89/0.99  fof(f80,plain,(
% 1.89/0.99    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f29])).
% 1.89/0.99  
% 1.89/0.99  fof(f83,plain,(
% 1.89/0.99    v4_lattice3(sK4)),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f6,axiom,(
% 1.89/0.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f24,plain,(
% 1.89/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f6])).
% 1.89/0.99  
% 1.89/0.99  fof(f25,plain,(
% 1.89/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f24])).
% 1.89/0.99  
% 1.89/0.99  fof(f74,plain,(
% 1.89/0.99    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f25])).
% 1.89/0.99  
% 1.89/0.99  fof(f5,axiom,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f22,plain,(
% 1.89/0.99    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f5])).
% 1.89/0.99  
% 1.89/0.99  fof(f23,plain,(
% 1.89/0.99    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f22])).
% 1.89/0.99  
% 1.89/0.99  fof(f41,plain,(
% 1.89/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f23])).
% 1.89/0.99  
% 1.89/0.99  fof(f42,plain,(
% 1.89/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f41])).
% 1.89/0.99  
% 1.89/0.99  fof(f43,plain,(
% 1.89/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(rectify,[],[f42])).
% 1.89/0.99  
% 1.89/0.99  fof(f44,plain,(
% 1.89/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f45,plain,(
% 1.89/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.89/0.99  
% 1.89/0.99  fof(f69,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f45])).
% 1.89/0.99  
% 1.89/0.99  fof(f89,plain,(
% 1.89/0.99    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f69])).
% 1.89/0.99  
% 1.89/0.99  fof(f7,axiom,(
% 1.89/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.89/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.99  
% 1.89/0.99  fof(f26,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.99    inference(ennf_transformation,[],[f7])).
% 1.89/0.99  
% 1.89/0.99  fof(f27,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f26])).
% 1.89/0.99  
% 1.89/0.99  fof(f46,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(nnf_transformation,[],[f27])).
% 1.89/0.99  
% 1.89/0.99  fof(f47,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(flattening,[],[f46])).
% 1.89/0.99  
% 1.89/0.99  fof(f48,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(rectify,[],[f47])).
% 1.89/0.99  
% 1.89/0.99  fof(f49,plain,(
% 1.89/0.99    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 1.89/0.99    introduced(choice_axiom,[])).
% 1.89/0.99  
% 1.89/0.99  fof(f50,plain,(
% 1.89/0.99    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 1.89/0.99  
% 1.89/0.99  fof(f75,plain,(
% 1.89/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(cnf_transformation,[],[f50])).
% 1.89/0.99  
% 1.89/0.99  fof(f91,plain,(
% 1.89/0.99    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.99    inference(equality_resolution,[],[f75])).
% 1.89/0.99  
% 1.89/0.99  fof(f87,plain,(
% 1.89/0.99    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f86,plain,(
% 1.89/0.99    r2_hidden(sK5,sK6)),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  fof(f85,plain,(
% 1.89/0.99    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.89/0.99    inference(cnf_transformation,[],[f54])).
% 1.89/0.99  
% 1.89/0.99  cnf(c_13,plain,
% 1.89/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 1.89/0.99      | r1_lattices(X0,X3,X1)
% 1.89/0.99      | ~ r2_hidden(X3,X2)
% 1.89/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_32,negated_conjecture,
% 1.89/0.99      ( ~ v2_struct_0(sK4) ),
% 1.89/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1040,plain,
% 1.89/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 1.89/0.99      | r1_lattices(X0,X3,X1)
% 1.89/0.99      | ~ r2_hidden(X3,X2)
% 1.89/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | sK4 != X0 ),
% 1.89/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1041,plain,
% 1.89/0.99      ( ~ r4_lattice3(sK4,X0,X1)
% 1.89/0.99      | r1_lattices(sK4,X2,X0)
% 1.89/0.99      | ~ r2_hidden(X2,X1)
% 1.89/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.89/0.99      | ~ l3_lattices(sK4) ),
% 1.89/0.99      inference(unflattening,[status(thm)],[c_1040]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_29,negated_conjecture,
% 1.89/0.99      ( l3_lattices(sK4) ),
% 1.89/0.99      inference(cnf_transformation,[],[f84]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1045,plain,
% 1.89/0.99      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/0.99      | ~ r2_hidden(X2,X1)
% 1.89/0.99      | r1_lattices(sK4,X2,X0)
% 1.89/0.99      | ~ r4_lattice3(sK4,X0,X1) ),
% 1.89/0.99      inference(global_propositional_subsumption,
% 1.89/0.99                [status(thm)],
% 1.89/0.99                [c_1041,c_29]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1046,plain,
% 1.89/0.99      ( ~ r4_lattice3(sK4,X0,X1)
% 1.89/0.99      | r1_lattices(sK4,X2,X0)
% 1.89/0.99      | ~ r2_hidden(X2,X1)
% 1.89/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 1.89/0.99      inference(renaming,[status(thm)],[c_1045]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2494,plain,
% 1.89/0.99      ( ~ r4_lattice3(sK4,X0_53,X0_54)
% 1.89/0.99      | r1_lattices(sK4,X1_53,X0_53)
% 1.89/0.99      | ~ r2_hidden(X1_53,X0_54)
% 1.89/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 1.89/0.99      inference(subtyping,[status(esa)],[c_1046]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3613,plain,
% 1.89/0.99      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),X0_54)
% 1.89/0.99      | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.89/0.99      | ~ r2_hidden(sK5,X0_54)
% 1.89/0.99      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_2494]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_3615,plain,
% 1.89/0.99      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
% 1.89/0.99      | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.89/0.99      | ~ r2_hidden(sK5,sK6)
% 1.89/0.99      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/0.99      inference(instantiation,[status(thm)],[c_3613]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_0,plain,
% 1.89/0.99      ( ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v10_lattices(X0)
% 1.89/0.99      | v9_lattices(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_4,plain,
% 1.89/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.89/0.99      | r3_lattices(X0,X1,X2)
% 1.89/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/0.99      | ~ v6_lattices(X0)
% 1.89/0.99      | ~ v8_lattices(X0)
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v9_lattices(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_397,plain,
% 1.89/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.89/0.99      | r3_lattices(X0,X1,X2)
% 1.89/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/0.99      | ~ v6_lattices(X0)
% 1.89/0.99      | ~ v8_lattices(X0)
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v10_lattices(X0) ),
% 1.89/0.99      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_2,plain,
% 1.89/0.99      ( v6_lattices(X0)
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v10_lattices(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_1,plain,
% 1.89/0.99      ( v8_lattices(X0)
% 1.89/0.99      | ~ l3_lattices(X0)
% 1.89/0.99      | v2_struct_0(X0)
% 1.89/0.99      | ~ v10_lattices(X0) ),
% 1.89/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.89/0.99  
% 1.89/0.99  cnf(c_401,plain,
% 1.89/0.99      ( ~ r1_lattices(X0,X1,X2)
% 1.89/0.99      | r3_lattices(X0,X1,X2)
% 1.89/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_397,c_2,c_1]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_31,negated_conjecture,
% 1.89/1.00      ( v10_lattices(sK4) ),
% 1.89/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_967,plain,
% 1.89/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.89/1.00      | r3_lattices(X0,X1,X2)
% 1.89/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_401,c_31]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_968,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,X0,X1)
% 1.89/1.00      | r3_lattices(sK4,X0,X1)
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.89/1.00      | ~ l3_lattices(sK4)
% 1.89/1.00      | v2_struct_0(sK4) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_967]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_972,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,X0,X1)
% 1.89/1.00      | r3_lattices(sK4,X0,X1)
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_968,c_32,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_973,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,X0,X1)
% 1.89/1.00      | r3_lattices(sK4,X0,X1)
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(renaming,[status(thm)],[c_972]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2497,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,X0_53,X1_53)
% 1.89/1.00      | r3_lattices(sK4,X0_53,X1_53)
% 1.89/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_973]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3422,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.89/1.00      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_9,plain,
% 1.89/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 1.89/1.00      | r1_lattices(X0,X1,X3)
% 1.89/1.00      | ~ r2_hidden(X3,X2)
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1130,plain,
% 1.89/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 1.89/1.00      | r1_lattices(X0,X1,X3)
% 1.89/1.00      | ~ r2_hidden(X3,X2)
% 1.89/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.89/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_32]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1131,plain,
% 1.89/1.00      ( ~ r3_lattice3(sK4,X0,X1)
% 1.89/1.00      | r1_lattices(sK4,X0,X2)
% 1.89/1.00      | ~ r2_hidden(X2,X1)
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.89/1.00      | ~ l3_lattices(sK4) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_1130]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1135,plain,
% 1.89/1.00      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/1.00      | ~ r2_hidden(X2,X1)
% 1.89/1.00      | r1_lattices(sK4,X0,X2)
% 1.89/1.00      | ~ r3_lattice3(sK4,X0,X1) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_1131,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1136,plain,
% 1.89/1.00      ( ~ r3_lattice3(sK4,X0,X1)
% 1.89/1.00      | r1_lattices(sK4,X0,X2)
% 1.89/1.00      | ~ r2_hidden(X2,X1)
% 1.89/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(renaming,[status(thm)],[c_1135]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2490,plain,
% 1.89/1.00      ( ~ r3_lattice3(sK4,X0_53,X0_54)
% 1.89/1.00      | r1_lattices(sK4,X0_53,X1_53)
% 1.89/1.00      | ~ r2_hidden(X1_53,X0_54)
% 1.89/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_1136]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3301,plain,
% 1.89/1.00      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),X0_54)
% 1.89/1.00      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.89/1.00      | ~ r2_hidden(sK5,X0_54)
% 1.89/1.00      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2490]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3306,plain,
% 1.89/1.00      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6)
% 1.89/1.00      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.89/1.00      | ~ r2_hidden(sK5,sK6)
% 1.89/1.00      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_3301]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_25,plain,
% 1.89/1.00      ( ~ v4_lattice3(X0)
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0)
% 1.89/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 1.89/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_30,negated_conjecture,
% 1.89/1.00      ( v4_lattice3(sK4) ),
% 1.89/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_700,plain,
% 1.89/1.00      ( ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0)
% 1.89/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_701,plain,
% 1.89/1.00      ( ~ l3_lattices(sK4)
% 1.89/1.00      | v2_struct_0(sK4)
% 1.89/1.00      | ~ v10_lattices(sK4)
% 1.89/1.00      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_700]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_705,plain,
% 1.89/1.00      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_701,c_32,c_31,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2506,plain,
% 1.89/1.00      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_54)) = k15_lattice3(sK4,X0_54) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_705]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_19,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1025,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1026,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 1.89/1.00      | ~ l3_lattices(sK4) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_1025]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_1030,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_1026,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2495,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_1030]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3003,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 1.89/1.00      inference(predicate_to_equality,[status(thm)],[c_2495]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3287,plain,
% 1.89/1.00      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) = iProver_top ),
% 1.89/1.00      inference(superposition,[status(thm)],[c_2506,c_3003]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3288,plain,
% 1.89/1.00      ( m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3287]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3290,plain,
% 1.89/1.00      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_3288]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_3228,plain,
% 1.89/1.00      ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.89/1.00      | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.89/1.00      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.89/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2497]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2566,plain,
% 1.89/1.00      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2495]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_18,plain,
% 1.89/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.89/1.00      | ~ v4_lattice3(X0)
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f89]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_807,plain,
% 1.89/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_808,plain,
% 1.89/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 1.89/1.00      | ~ l3_lattices(sK4)
% 1.89/1.00      | v2_struct_0(sK4)
% 1.89/1.00      | ~ v10_lattices(sK4) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_807]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_812,plain,
% 1.89/1.00      ( ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 1.89/1.00      | r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_808,c_32,c_31,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_813,plain,
% 1.89/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(renaming,[status(thm)],[c_812]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2502,plain,
% 1.89/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_54),X0_54)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(sK4,X0_54),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_813]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2545,plain,
% 1.89/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
% 1.89/1.00      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2502]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_24,plain,
% 1.89/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.89/1.00      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.89/1.00      | ~ v4_lattice3(X0)
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0) ),
% 1.89/1.00      inference(cnf_transformation,[],[f91]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_191,plain,
% 1.89/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.89/1.00      | ~ v4_lattice3(X0)
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_24,c_19]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_685,plain,
% 1.89/1.00      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.89/1.00      | ~ l3_lattices(X0)
% 1.89/1.00      | v2_struct_0(X0)
% 1.89/1.00      | ~ v10_lattices(X0)
% 1.89/1.00      | sK4 != X0 ),
% 1.89/1.00      inference(resolution_lifted,[status(thm)],[c_191,c_30]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_686,plain,
% 1.89/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
% 1.89/1.00      | ~ l3_lattices(sK4)
% 1.89/1.00      | v2_struct_0(sK4)
% 1.89/1.00      | ~ v10_lattices(sK4) ),
% 1.89/1.00      inference(unflattening,[status(thm)],[c_685]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_690,plain,
% 1.89/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
% 1.89/1.00      inference(global_propositional_subsumption,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_686,c_32,c_31,c_29]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2507,plain,
% 1.89/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_54),X0_54) ),
% 1.89/1.00      inference(subtyping,[status(esa)],[c_690]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_2532,plain,
% 1.89/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) ),
% 1.89/1.00      inference(instantiation,[status(thm)],[c_2507]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_26,negated_conjecture,
% 1.89/1.00      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.89/1.00      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
% 1.89/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_27,negated_conjecture,
% 1.89/1.00      ( r2_hidden(sK5,sK6) ),
% 1.89/1.00      inference(cnf_transformation,[],[f86]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(c_28,negated_conjecture,
% 1.89/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.89/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.89/1.00  
% 1.89/1.00  cnf(contradiction,plain,
% 1.89/1.00      ( $false ),
% 1.89/1.00      inference(minisat,
% 1.89/1.00                [status(thm)],
% 1.89/1.00                [c_3615,c_3422,c_3306,c_3290,c_3228,c_2566,c_2545,c_2532,
% 1.89/1.00                 c_26,c_27,c_28]) ).
% 1.89/1.00  
% 1.89/1.00  
% 1.89/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/1.00  
% 1.89/1.00  ------                               Statistics
% 1.89/1.00  
% 1.89/1.00  ------ General
% 1.89/1.00  
% 1.89/1.00  abstr_ref_over_cycles:                  0
% 1.89/1.00  abstr_ref_under_cycles:                 0
% 1.89/1.00  gc_basic_clause_elim:                   0
% 1.89/1.00  forced_gc_time:                         0
% 1.89/1.00  parsing_time:                           0.01
% 1.89/1.00  unif_index_cands_time:                  0.
% 1.89/1.00  unif_index_add_time:                    0.
% 1.89/1.00  orderings_time:                         0.
% 1.89/1.00  out_proof_time:                         0.014
% 1.89/1.00  total_time:                             0.149
% 1.89/1.00  num_of_symbols:                         56
% 2.00/1.00  num_of_terms:                           2598
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing
% 2.00/1.00  
% 2.00/1.00  num_of_splits:                          0
% 2.00/1.00  num_of_split_atoms:                     0
% 2.00/1.00  num_of_reused_defs:                     0
% 2.00/1.00  num_eq_ax_congr_red:                    60
% 2.00/1.00  num_of_sem_filtered_clauses:            1
% 2.00/1.00  num_of_subtypes:                        4
% 2.00/1.00  monotx_restored_types:                  0
% 2.00/1.00  sat_num_of_epr_types:                   0
% 2.00/1.00  sat_num_of_non_cyclic_types:            0
% 2.00/1.00  sat_guarded_non_collapsed_types:        1
% 2.00/1.00  num_pure_diseq_elim:                    0
% 2.00/1.00  simp_replaced_by:                       0
% 2.00/1.00  res_preprocessed:                       124
% 2.00/1.00  prep_upred:                             0
% 2.00/1.00  prep_unflattend:                        116
% 2.00/1.00  smt_new_axioms:                         0
% 2.00/1.00  pred_elim_cands:                        6
% 2.00/1.00  pred_elim:                              7
% 2.00/1.00  pred_elim_cl:                           7
% 2.00/1.00  pred_elim_cycles:                       12
% 2.00/1.00  merged_defs:                            0
% 2.00/1.00  merged_defs_ncl:                        0
% 2.00/1.00  bin_hyper_res:                          0
% 2.00/1.00  prep_cycles:                            4
% 2.00/1.00  pred_elim_time:                         0.043
% 2.00/1.00  splitting_time:                         0.
% 2.00/1.00  sem_filter_time:                        0.
% 2.00/1.00  monotx_time:                            0.
% 2.00/1.00  subtype_inf_time:                       0.
% 2.00/1.00  
% 2.00/1.00  ------ Problem properties
% 2.00/1.00  
% 2.00/1.00  clauses:                                25
% 2.00/1.00  conjectures:                            3
% 2.00/1.00  epr:                                    1
% 2.00/1.00  horn:                                   17
% 2.00/1.00  ground:                                 3
% 2.00/1.00  unary:                                  5
% 2.00/1.00  binary:                                 2
% 2.00/1.00  lits:                                   76
% 2.00/1.00  lits_eq:                                7
% 2.00/1.00  fd_pure:                                0
% 2.00/1.00  fd_pseudo:                              0
% 2.00/1.00  fd_cond:                                0
% 2.00/1.00  fd_pseudo_cond:                         6
% 2.00/1.00  ac_symbols:                             0
% 2.00/1.00  
% 2.00/1.00  ------ Propositional Solver
% 2.00/1.00  
% 2.00/1.00  prop_solver_calls:                      25
% 2.00/1.00  prop_fast_solver_calls:                 1512
% 2.00/1.00  smt_solver_calls:                       0
% 2.00/1.00  smt_fast_solver_calls:                  0
% 2.00/1.00  prop_num_of_clauses:                    796
% 2.00/1.00  prop_preprocess_simplified:             4314
% 2.00/1.00  prop_fo_subsumed:                       79
% 2.00/1.00  prop_solver_time:                       0.
% 2.00/1.00  smt_solver_time:                        0.
% 2.00/1.00  smt_fast_solver_time:                   0.
% 2.00/1.00  prop_fast_solver_time:                  0.
% 2.00/1.00  prop_unsat_core_time:                   0.
% 2.00/1.00  
% 2.00/1.00  ------ QBF
% 2.00/1.00  
% 2.00/1.00  qbf_q_res:                              0
% 2.00/1.00  qbf_num_tautologies:                    0
% 2.00/1.00  qbf_prep_cycles:                        0
% 2.00/1.00  
% 2.00/1.00  ------ BMC1
% 2.00/1.00  
% 2.00/1.00  bmc1_current_bound:                     -1
% 2.00/1.00  bmc1_last_solved_bound:                 -1
% 2.00/1.00  bmc1_unsat_core_size:                   -1
% 2.00/1.00  bmc1_unsat_core_parents_size:           -1
% 2.00/1.00  bmc1_merge_next_fun:                    0
% 2.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation
% 2.00/1.00  
% 2.00/1.00  inst_num_of_clauses:                    101
% 2.00/1.00  inst_num_in_passive:                    30
% 2.00/1.00  inst_num_in_active:                     68
% 2.00/1.00  inst_num_in_unprocessed:                2
% 2.00/1.00  inst_num_of_loops:                      75
% 2.00/1.00  inst_num_of_learning_restarts:          0
% 2.00/1.00  inst_num_moves_active_passive:          4
% 2.00/1.00  inst_lit_activity:                      0
% 2.00/1.00  inst_lit_activity_moves:                0
% 2.00/1.00  inst_num_tautologies:                   0
% 2.00/1.00  inst_num_prop_implied:                  0
% 2.00/1.00  inst_num_existing_simplified:           0
% 2.00/1.00  inst_num_eq_res_simplified:             0
% 2.00/1.00  inst_num_child_elim:                    0
% 2.00/1.00  inst_num_of_dismatching_blockings:      5
% 2.00/1.00  inst_num_of_non_proper_insts:           71
% 2.00/1.00  inst_num_of_duplicates:                 0
% 2.00/1.00  inst_inst_num_from_inst_to_res:         0
% 2.00/1.00  inst_dismatching_checking_time:         0.
% 2.00/1.00  
% 2.00/1.00  ------ Resolution
% 2.00/1.00  
% 2.00/1.00  res_num_of_clauses:                     0
% 2.00/1.00  res_num_in_passive:                     0
% 2.00/1.00  res_num_in_active:                      0
% 2.00/1.00  res_num_of_loops:                       128
% 2.00/1.00  res_forward_subset_subsumed:            10
% 2.00/1.00  res_backward_subset_subsumed:           0
% 2.00/1.00  res_forward_subsumed:                   0
% 2.00/1.00  res_backward_subsumed:                  0
% 2.00/1.00  res_forward_subsumption_resolution:     7
% 2.00/1.00  res_backward_subsumption_resolution:    1
% 2.00/1.00  res_clause_to_clause_subsumption:       108
% 2.00/1.00  res_orphan_elimination:                 0
% 2.00/1.00  res_tautology_del:                      7
% 2.00/1.00  res_num_eq_res_simplified:              0
% 2.00/1.00  res_num_sel_changes:                    0
% 2.00/1.00  res_moves_from_active_to_pass:          0
% 2.00/1.00  
% 2.00/1.00  ------ Superposition
% 2.00/1.00  
% 2.00/1.00  sup_time_total:                         0.
% 2.00/1.00  sup_time_generating:                    0.
% 2.00/1.00  sup_time_sim_full:                      0.
% 2.00/1.00  sup_time_sim_immed:                     0.
% 2.00/1.00  
% 2.00/1.00  sup_num_of_clauses:                     27
% 2.00/1.00  sup_num_in_active:                      14
% 2.00/1.00  sup_num_in_passive:                     13
% 2.00/1.00  sup_num_of_loops:                       14
% 2.00/1.00  sup_fw_superposition:                   2
% 2.00/1.00  sup_bw_superposition:                   0
% 2.00/1.00  sup_immediate_simplified:               0
% 2.00/1.00  sup_given_eliminated:                   0
% 2.00/1.00  comparisons_done:                       0
% 2.00/1.00  comparisons_avoided:                    0
% 2.00/1.00  
% 2.00/1.00  ------ Simplifications
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  sim_fw_subset_subsumed:                 0
% 2.00/1.00  sim_bw_subset_subsumed:                 0
% 2.00/1.00  sim_fw_subsumed:                        0
% 2.00/1.00  sim_bw_subsumed:                        0
% 2.00/1.00  sim_fw_subsumption_res:                 0
% 2.00/1.00  sim_bw_subsumption_res:                 0
% 2.00/1.00  sim_tautology_del:                      0
% 2.00/1.00  sim_eq_tautology_del:                   0
% 2.00/1.00  sim_eq_res_simp:                        0
% 2.00/1.00  sim_fw_demodulated:                     0
% 2.00/1.00  sim_bw_demodulated:                     0
% 2.00/1.00  sim_light_normalised:                   0
% 2.00/1.00  sim_joinable_taut:                      0
% 2.00/1.00  sim_joinable_simp:                      0
% 2.00/1.00  sim_ac_normalised:                      0
% 2.00/1.00  sim_smt_subsumption:                    0
% 2.00/1.00  
%------------------------------------------------------------------------------
