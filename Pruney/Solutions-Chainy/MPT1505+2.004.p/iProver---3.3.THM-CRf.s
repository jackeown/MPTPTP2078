%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:10 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 425 expanded)
%              Number of clauses        :   65 (  96 expanded)
%              Number of leaves         :   16 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  824 (2931 expanded)
%              Number of equality atoms :   31 (  32 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f82,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f76,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f83,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f54])).

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

cnf(c_403,plain,
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

cnf(c_407,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_2,c_1])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_957,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_407,c_31])).

cnf(c_958,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_962,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_32,c_29])).

cnf(c_963,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_962])).

cnf(c_2502,plain,
    ( ~ r1_lattices(sK4,X0_52,X1_52)
    | r3_lattices(sK4,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_963])).

cnf(c_3389,plain,
    ( ~ r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
    | r3_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_3391,plain,
    ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3389])).

cnf(c_3371,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
    | r3_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_3373,plain,
    ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1045,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_1046,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1045])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1046,c_29])).

cnf(c_1051,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1050])).

cnf(c_2498,plain,
    ( ~ r4_lattice3(sK4,X0_52,X0_53)
    | r1_lattices(sK4,X1_52,X0_52)
    | ~ r2_hidden(X1_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1051])).

cnf(c_3253,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_53),X0_53)
    | r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
    | ~ r2_hidden(X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_3255,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
    | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3253])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1135,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_1136,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_29])).

cnf(c_1141,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1140])).

cnf(c_2494,plain,
    ( ~ r3_lattice3(sK4,X0_52,X0_53)
    | r1_lattices(sK4,X0_52,X1_52)
    | ~ r2_hidden(X1_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1141])).

cnf(c_3248,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,X0_53),X0_53)
    | r1_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
    | ~ r2_hidden(X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_3250,plain,
    ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6)
    | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ r2_hidden(sK5,sK6)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_19,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1030,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_1031,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1035,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_29])).

cnf(c_2499,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1035])).

cnf(c_2568,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_20,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1015,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_1016,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1015])).

cnf(c_1020,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_29])).

cnf(c_2500,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1020])).

cnf(c_2565,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2500])).

cnf(c_25,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_190,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_20])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_706,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_30])).

cnf(c_707,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_711,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_32,c_31,c_29])).

cnf(c_2509,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_711])).

cnf(c_2538,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_18,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_203,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_691,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_30])).

cnf(c_692,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_696,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_32,c_31,c_29])).

cnf(c_2510,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_696])).

cnf(c_2535,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2510])).

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
    inference(minisat,[status(thm)],[c_3391,c_3373,c_3255,c_3250,c_2568,c_2565,c_2538,c_2535,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.30/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.30/1.05  
% 1.30/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.30/1.05  
% 1.30/1.05  ------  iProver source info
% 1.30/1.05  
% 1.30/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.30/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.30/1.05  git: non_committed_changes: false
% 1.30/1.05  git: last_make_outside_of_git: false
% 1.30/1.05  
% 1.30/1.05  ------ 
% 1.30/1.05  
% 1.30/1.05  ------ Input Options
% 1.30/1.05  
% 1.30/1.05  --out_options                           all
% 1.30/1.05  --tptp_safe_out                         true
% 1.30/1.05  --problem_path                          ""
% 1.30/1.05  --include_path                          ""
% 1.30/1.05  --clausifier                            res/vclausify_rel
% 1.30/1.05  --clausifier_options                    --mode clausify
% 1.30/1.05  --stdin                                 false
% 1.30/1.05  --stats_out                             all
% 1.30/1.05  
% 1.30/1.05  ------ General Options
% 1.30/1.05  
% 1.30/1.05  --fof                                   false
% 1.30/1.05  --time_out_real                         305.
% 1.30/1.05  --time_out_virtual                      -1.
% 1.30/1.05  --symbol_type_check                     false
% 1.30/1.05  --clausify_out                          false
% 1.30/1.05  --sig_cnt_out                           false
% 1.30/1.05  --trig_cnt_out                          false
% 1.30/1.05  --trig_cnt_out_tolerance                1.
% 1.30/1.05  --trig_cnt_out_sk_spl                   false
% 1.30/1.05  --abstr_cl_out                          false
% 1.30/1.05  
% 1.30/1.05  ------ Global Options
% 1.30/1.05  
% 1.30/1.05  --schedule                              default
% 1.30/1.05  --add_important_lit                     false
% 1.30/1.05  --prop_solver_per_cl                    1000
% 1.30/1.05  --min_unsat_core                        false
% 1.30/1.05  --soft_assumptions                      false
% 1.30/1.05  --soft_lemma_size                       3
% 1.30/1.05  --prop_impl_unit_size                   0
% 1.30/1.05  --prop_impl_unit                        []
% 1.30/1.05  --share_sel_clauses                     true
% 1.30/1.05  --reset_solvers                         false
% 1.30/1.05  --bc_imp_inh                            [conj_cone]
% 1.30/1.05  --conj_cone_tolerance                   3.
% 1.30/1.05  --extra_neg_conj                        none
% 1.30/1.05  --large_theory_mode                     true
% 1.30/1.05  --prolific_symb_bound                   200
% 1.30/1.05  --lt_threshold                          2000
% 1.30/1.05  --clause_weak_htbl                      true
% 1.30/1.05  --gc_record_bc_elim                     false
% 1.30/1.05  
% 1.30/1.05  ------ Preprocessing Options
% 1.30/1.05  
% 1.30/1.05  --preprocessing_flag                    true
% 1.30/1.05  --time_out_prep_mult                    0.1
% 1.30/1.05  --splitting_mode                        input
% 1.30/1.05  --splitting_grd                         true
% 1.30/1.05  --splitting_cvd                         false
% 1.30/1.05  --splitting_cvd_svl                     false
% 1.30/1.05  --splitting_nvd                         32
% 1.30/1.05  --sub_typing                            true
% 1.30/1.05  --prep_gs_sim                           true
% 1.30/1.05  --prep_unflatten                        true
% 1.30/1.05  --prep_res_sim                          true
% 1.30/1.05  --prep_upred                            true
% 1.30/1.05  --prep_sem_filter                       exhaustive
% 1.30/1.05  --prep_sem_filter_out                   false
% 1.30/1.05  --pred_elim                             true
% 1.30/1.05  --res_sim_input                         true
% 1.30/1.05  --eq_ax_congr_red                       true
% 1.30/1.05  --pure_diseq_elim                       true
% 1.30/1.05  --brand_transform                       false
% 1.30/1.05  --non_eq_to_eq                          false
% 1.30/1.05  --prep_def_merge                        true
% 1.30/1.05  --prep_def_merge_prop_impl              false
% 1.30/1.05  --prep_def_merge_mbd                    true
% 1.30/1.05  --prep_def_merge_tr_red                 false
% 1.30/1.05  --prep_def_merge_tr_cl                  false
% 1.30/1.05  --smt_preprocessing                     true
% 1.30/1.05  --smt_ac_axioms                         fast
% 1.30/1.05  --preprocessed_out                      false
% 1.30/1.05  --preprocessed_stats                    false
% 1.30/1.05  
% 1.30/1.05  ------ Abstraction refinement Options
% 1.30/1.05  
% 1.30/1.05  --abstr_ref                             []
% 1.30/1.05  --abstr_ref_prep                        false
% 1.30/1.05  --abstr_ref_until_sat                   false
% 1.30/1.05  --abstr_ref_sig_restrict                funpre
% 1.30/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.05  --abstr_ref_under                       []
% 1.30/1.05  
% 1.30/1.05  ------ SAT Options
% 1.30/1.05  
% 1.30/1.05  --sat_mode                              false
% 1.30/1.05  --sat_fm_restart_options                ""
% 1.30/1.05  --sat_gr_def                            false
% 1.30/1.05  --sat_epr_types                         true
% 1.30/1.05  --sat_non_cyclic_types                  false
% 1.30/1.05  --sat_finite_models                     false
% 1.30/1.05  --sat_fm_lemmas                         false
% 1.30/1.05  --sat_fm_prep                           false
% 1.30/1.05  --sat_fm_uc_incr                        true
% 1.30/1.05  --sat_out_model                         small
% 1.30/1.05  --sat_out_clauses                       false
% 1.30/1.05  
% 1.30/1.05  ------ QBF Options
% 1.30/1.05  
% 1.30/1.05  --qbf_mode                              false
% 1.30/1.05  --qbf_elim_univ                         false
% 1.30/1.05  --qbf_dom_inst                          none
% 1.30/1.05  --qbf_dom_pre_inst                      false
% 1.30/1.05  --qbf_sk_in                             false
% 1.30/1.05  --qbf_pred_elim                         true
% 1.30/1.05  --qbf_split                             512
% 1.30/1.05  
% 1.30/1.05  ------ BMC1 Options
% 1.30/1.05  
% 1.30/1.05  --bmc1_incremental                      false
% 1.30/1.05  --bmc1_axioms                           reachable_all
% 1.30/1.05  --bmc1_min_bound                        0
% 1.30/1.05  --bmc1_max_bound                        -1
% 1.30/1.05  --bmc1_max_bound_default                -1
% 1.30/1.05  --bmc1_symbol_reachability              true
% 1.30/1.05  --bmc1_property_lemmas                  false
% 1.30/1.05  --bmc1_k_induction                      false
% 1.30/1.05  --bmc1_non_equiv_states                 false
% 1.30/1.05  --bmc1_deadlock                         false
% 1.30/1.05  --bmc1_ucm                              false
% 1.30/1.05  --bmc1_add_unsat_core                   none
% 1.30/1.05  --bmc1_unsat_core_children              false
% 1.30/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.05  --bmc1_out_stat                         full
% 1.30/1.05  --bmc1_ground_init                      false
% 1.30/1.05  --bmc1_pre_inst_next_state              false
% 1.30/1.05  --bmc1_pre_inst_state                   false
% 1.30/1.05  --bmc1_pre_inst_reach_state             false
% 1.30/1.05  --bmc1_out_unsat_core                   false
% 1.30/1.05  --bmc1_aig_witness_out                  false
% 1.30/1.05  --bmc1_verbose                          false
% 1.30/1.05  --bmc1_dump_clauses_tptp                false
% 1.30/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.05  --bmc1_dump_file                        -
% 1.30/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.05  --bmc1_ucm_extend_mode                  1
% 1.30/1.05  --bmc1_ucm_init_mode                    2
% 1.30/1.05  --bmc1_ucm_cone_mode                    none
% 1.30/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.05  --bmc1_ucm_relax_model                  4
% 1.30/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.05  --bmc1_ucm_layered_model                none
% 1.30/1.05  --bmc1_ucm_max_lemma_size               10
% 1.30/1.05  
% 1.30/1.05  ------ AIG Options
% 1.30/1.05  
% 1.30/1.05  --aig_mode                              false
% 1.30/1.05  
% 1.30/1.05  ------ Instantiation Options
% 1.30/1.05  
% 1.30/1.05  --instantiation_flag                    true
% 1.30/1.05  --inst_sos_flag                         false
% 1.30/1.05  --inst_sos_phase                        true
% 1.30/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.05  --inst_lit_sel_side                     num_symb
% 1.30/1.05  --inst_solver_per_active                1400
% 1.30/1.05  --inst_solver_calls_frac                1.
% 1.30/1.05  --inst_passive_queue_type               priority_queues
% 1.30/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.05  --inst_passive_queues_freq              [25;2]
% 1.30/1.05  --inst_dismatching                      true
% 1.30/1.05  --inst_eager_unprocessed_to_passive     true
% 1.30/1.05  --inst_prop_sim_given                   true
% 1.30/1.05  --inst_prop_sim_new                     false
% 1.30/1.05  --inst_subs_new                         false
% 1.30/1.05  --inst_eq_res_simp                      false
% 1.30/1.05  --inst_subs_given                       false
% 1.30/1.05  --inst_orphan_elimination               true
% 1.30/1.05  --inst_learning_loop_flag               true
% 1.30/1.05  --inst_learning_start                   3000
% 1.30/1.05  --inst_learning_factor                  2
% 1.30/1.05  --inst_start_prop_sim_after_learn       3
% 1.30/1.05  --inst_sel_renew                        solver
% 1.30/1.05  --inst_lit_activity_flag                true
% 1.30/1.05  --inst_restr_to_given                   false
% 1.30/1.05  --inst_activity_threshold               500
% 1.30/1.05  --inst_out_proof                        true
% 1.30/1.05  
% 1.30/1.05  ------ Resolution Options
% 1.30/1.05  
% 1.30/1.05  --resolution_flag                       true
% 1.30/1.05  --res_lit_sel                           adaptive
% 1.30/1.05  --res_lit_sel_side                      none
% 1.30/1.05  --res_ordering                          kbo
% 1.30/1.05  --res_to_prop_solver                    active
% 1.30/1.05  --res_prop_simpl_new                    false
% 1.30/1.05  --res_prop_simpl_given                  true
% 1.30/1.05  --res_passive_queue_type                priority_queues
% 1.30/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.05  --res_passive_queues_freq               [15;5]
% 1.30/1.05  --res_forward_subs                      full
% 1.30/1.05  --res_backward_subs                     full
% 1.30/1.05  --res_forward_subs_resolution           true
% 1.30/1.05  --res_backward_subs_resolution          true
% 1.30/1.05  --res_orphan_elimination                true
% 1.30/1.05  --res_time_limit                        2.
% 1.30/1.05  --res_out_proof                         true
% 1.30/1.05  
% 1.30/1.05  ------ Superposition Options
% 1.30/1.05  
% 1.30/1.05  --superposition_flag                    true
% 1.30/1.05  --sup_passive_queue_type                priority_queues
% 1.30/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.05  --demod_completeness_check              fast
% 1.30/1.05  --demod_use_ground                      true
% 1.30/1.05  --sup_to_prop_solver                    passive
% 1.30/1.05  --sup_prop_simpl_new                    true
% 1.30/1.05  --sup_prop_simpl_given                  true
% 1.30/1.05  --sup_fun_splitting                     false
% 1.30/1.05  --sup_smt_interval                      50000
% 1.30/1.05  
% 1.30/1.05  ------ Superposition Simplification Setup
% 1.30/1.05  
% 1.30/1.05  --sup_indices_passive                   []
% 1.30/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_full_bw                           [BwDemod]
% 1.30/1.05  --sup_immed_triv                        [TrivRules]
% 1.30/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_immed_bw_main                     []
% 1.30/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.05  
% 1.30/1.05  ------ Combination Options
% 1.30/1.05  
% 1.30/1.05  --comb_res_mult                         3
% 1.30/1.05  --comb_sup_mult                         2
% 1.30/1.05  --comb_inst_mult                        10
% 1.30/1.05  
% 1.30/1.05  ------ Debug Options
% 1.30/1.05  
% 1.30/1.05  --dbg_backtrace                         false
% 1.30/1.05  --dbg_dump_prop_clauses                 false
% 1.30/1.05  --dbg_dump_prop_clauses_file            -
% 1.30/1.05  --dbg_out_stat                          false
% 1.30/1.05  ------ Parsing...
% 1.30/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.30/1.05  
% 1.30/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.30/1.05  
% 1.30/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.30/1.05  
% 1.30/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.30/1.05  ------ Proving...
% 1.30/1.05  ------ Problem Properties 
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  clauses                                 25
% 1.30/1.05  conjectures                             3
% 1.30/1.05  EPR                                     1
% 1.30/1.05  Horn                                    17
% 1.30/1.05  unary                                   6
% 1.30/1.05  binary                                  1
% 1.30/1.05  lits                                    74
% 1.30/1.05  lits eq                                 6
% 1.30/1.05  fd_pure                                 0
% 1.30/1.05  fd_pseudo                               0
% 1.30/1.05  fd_cond                                 0
% 1.30/1.05  fd_pseudo_cond                          6
% 1.30/1.05  AC symbols                              0
% 1.30/1.05  
% 1.30/1.05  ------ Schedule dynamic 5 is on 
% 1.30/1.05  
% 1.30/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  ------ 
% 1.30/1.05  Current options:
% 1.30/1.05  ------ 
% 1.30/1.05  
% 1.30/1.05  ------ Input Options
% 1.30/1.05  
% 1.30/1.05  --out_options                           all
% 1.30/1.05  --tptp_safe_out                         true
% 1.30/1.05  --problem_path                          ""
% 1.30/1.05  --include_path                          ""
% 1.30/1.05  --clausifier                            res/vclausify_rel
% 1.30/1.05  --clausifier_options                    --mode clausify
% 1.30/1.05  --stdin                                 false
% 1.30/1.05  --stats_out                             all
% 1.30/1.05  
% 1.30/1.05  ------ General Options
% 1.30/1.05  
% 1.30/1.05  --fof                                   false
% 1.30/1.05  --time_out_real                         305.
% 1.30/1.05  --time_out_virtual                      -1.
% 1.30/1.05  --symbol_type_check                     false
% 1.30/1.05  --clausify_out                          false
% 1.30/1.05  --sig_cnt_out                           false
% 1.30/1.05  --trig_cnt_out                          false
% 1.30/1.05  --trig_cnt_out_tolerance                1.
% 1.30/1.05  --trig_cnt_out_sk_spl                   false
% 1.30/1.05  --abstr_cl_out                          false
% 1.30/1.05  
% 1.30/1.05  ------ Global Options
% 1.30/1.05  
% 1.30/1.05  --schedule                              default
% 1.30/1.05  --add_important_lit                     false
% 1.30/1.05  --prop_solver_per_cl                    1000
% 1.30/1.05  --min_unsat_core                        false
% 1.30/1.05  --soft_assumptions                      false
% 1.30/1.05  --soft_lemma_size                       3
% 1.30/1.05  --prop_impl_unit_size                   0
% 1.30/1.05  --prop_impl_unit                        []
% 1.30/1.05  --share_sel_clauses                     true
% 1.30/1.05  --reset_solvers                         false
% 1.30/1.05  --bc_imp_inh                            [conj_cone]
% 1.30/1.05  --conj_cone_tolerance                   3.
% 1.30/1.05  --extra_neg_conj                        none
% 1.30/1.05  --large_theory_mode                     true
% 1.30/1.05  --prolific_symb_bound                   200
% 1.30/1.05  --lt_threshold                          2000
% 1.30/1.05  --clause_weak_htbl                      true
% 1.30/1.05  --gc_record_bc_elim                     false
% 1.30/1.05  
% 1.30/1.05  ------ Preprocessing Options
% 1.30/1.05  
% 1.30/1.05  --preprocessing_flag                    true
% 1.30/1.05  --time_out_prep_mult                    0.1
% 1.30/1.05  --splitting_mode                        input
% 1.30/1.05  --splitting_grd                         true
% 1.30/1.05  --splitting_cvd                         false
% 1.30/1.05  --splitting_cvd_svl                     false
% 1.30/1.05  --splitting_nvd                         32
% 1.30/1.05  --sub_typing                            true
% 1.30/1.05  --prep_gs_sim                           true
% 1.30/1.05  --prep_unflatten                        true
% 1.30/1.05  --prep_res_sim                          true
% 1.30/1.05  --prep_upred                            true
% 1.30/1.05  --prep_sem_filter                       exhaustive
% 1.30/1.05  --prep_sem_filter_out                   false
% 1.30/1.05  --pred_elim                             true
% 1.30/1.05  --res_sim_input                         true
% 1.30/1.05  --eq_ax_congr_red                       true
% 1.30/1.05  --pure_diseq_elim                       true
% 1.30/1.05  --brand_transform                       false
% 1.30/1.05  --non_eq_to_eq                          false
% 1.30/1.05  --prep_def_merge                        true
% 1.30/1.05  --prep_def_merge_prop_impl              false
% 1.30/1.05  --prep_def_merge_mbd                    true
% 1.30/1.05  --prep_def_merge_tr_red                 false
% 1.30/1.05  --prep_def_merge_tr_cl                  false
% 1.30/1.05  --smt_preprocessing                     true
% 1.30/1.05  --smt_ac_axioms                         fast
% 1.30/1.05  --preprocessed_out                      false
% 1.30/1.05  --preprocessed_stats                    false
% 1.30/1.05  
% 1.30/1.05  ------ Abstraction refinement Options
% 1.30/1.05  
% 1.30/1.05  --abstr_ref                             []
% 1.30/1.05  --abstr_ref_prep                        false
% 1.30/1.05  --abstr_ref_until_sat                   false
% 1.30/1.05  --abstr_ref_sig_restrict                funpre
% 1.30/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.05  --abstr_ref_under                       []
% 1.30/1.05  
% 1.30/1.05  ------ SAT Options
% 1.30/1.05  
% 1.30/1.05  --sat_mode                              false
% 1.30/1.05  --sat_fm_restart_options                ""
% 1.30/1.05  --sat_gr_def                            false
% 1.30/1.05  --sat_epr_types                         true
% 1.30/1.05  --sat_non_cyclic_types                  false
% 1.30/1.05  --sat_finite_models                     false
% 1.30/1.05  --sat_fm_lemmas                         false
% 1.30/1.05  --sat_fm_prep                           false
% 1.30/1.05  --sat_fm_uc_incr                        true
% 1.30/1.05  --sat_out_model                         small
% 1.30/1.05  --sat_out_clauses                       false
% 1.30/1.05  
% 1.30/1.05  ------ QBF Options
% 1.30/1.05  
% 1.30/1.05  --qbf_mode                              false
% 1.30/1.05  --qbf_elim_univ                         false
% 1.30/1.05  --qbf_dom_inst                          none
% 1.30/1.05  --qbf_dom_pre_inst                      false
% 1.30/1.05  --qbf_sk_in                             false
% 1.30/1.05  --qbf_pred_elim                         true
% 1.30/1.05  --qbf_split                             512
% 1.30/1.05  
% 1.30/1.05  ------ BMC1 Options
% 1.30/1.05  
% 1.30/1.05  --bmc1_incremental                      false
% 1.30/1.05  --bmc1_axioms                           reachable_all
% 1.30/1.05  --bmc1_min_bound                        0
% 1.30/1.05  --bmc1_max_bound                        -1
% 1.30/1.05  --bmc1_max_bound_default                -1
% 1.30/1.05  --bmc1_symbol_reachability              true
% 1.30/1.05  --bmc1_property_lemmas                  false
% 1.30/1.05  --bmc1_k_induction                      false
% 1.30/1.05  --bmc1_non_equiv_states                 false
% 1.30/1.05  --bmc1_deadlock                         false
% 1.30/1.05  --bmc1_ucm                              false
% 1.30/1.05  --bmc1_add_unsat_core                   none
% 1.30/1.05  --bmc1_unsat_core_children              false
% 1.30/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.05  --bmc1_out_stat                         full
% 1.30/1.05  --bmc1_ground_init                      false
% 1.30/1.05  --bmc1_pre_inst_next_state              false
% 1.30/1.05  --bmc1_pre_inst_state                   false
% 1.30/1.05  --bmc1_pre_inst_reach_state             false
% 1.30/1.05  --bmc1_out_unsat_core                   false
% 1.30/1.05  --bmc1_aig_witness_out                  false
% 1.30/1.05  --bmc1_verbose                          false
% 1.30/1.05  --bmc1_dump_clauses_tptp                false
% 1.30/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.05  --bmc1_dump_file                        -
% 1.30/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.05  --bmc1_ucm_extend_mode                  1
% 1.30/1.05  --bmc1_ucm_init_mode                    2
% 1.30/1.05  --bmc1_ucm_cone_mode                    none
% 1.30/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.05  --bmc1_ucm_relax_model                  4
% 1.30/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.05  --bmc1_ucm_layered_model                none
% 1.30/1.05  --bmc1_ucm_max_lemma_size               10
% 1.30/1.05  
% 1.30/1.05  ------ AIG Options
% 1.30/1.05  
% 1.30/1.05  --aig_mode                              false
% 1.30/1.05  
% 1.30/1.05  ------ Instantiation Options
% 1.30/1.05  
% 1.30/1.05  --instantiation_flag                    true
% 1.30/1.05  --inst_sos_flag                         false
% 1.30/1.05  --inst_sos_phase                        true
% 1.30/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.05  --inst_lit_sel_side                     none
% 1.30/1.05  --inst_solver_per_active                1400
% 1.30/1.05  --inst_solver_calls_frac                1.
% 1.30/1.05  --inst_passive_queue_type               priority_queues
% 1.30/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.05  --inst_passive_queues_freq              [25;2]
% 1.30/1.05  --inst_dismatching                      true
% 1.30/1.05  --inst_eager_unprocessed_to_passive     true
% 1.30/1.05  --inst_prop_sim_given                   true
% 1.30/1.05  --inst_prop_sim_new                     false
% 1.30/1.05  --inst_subs_new                         false
% 1.30/1.05  --inst_eq_res_simp                      false
% 1.30/1.05  --inst_subs_given                       false
% 1.30/1.05  --inst_orphan_elimination               true
% 1.30/1.05  --inst_learning_loop_flag               true
% 1.30/1.05  --inst_learning_start                   3000
% 1.30/1.05  --inst_learning_factor                  2
% 1.30/1.05  --inst_start_prop_sim_after_learn       3
% 1.30/1.05  --inst_sel_renew                        solver
% 1.30/1.05  --inst_lit_activity_flag                true
% 1.30/1.05  --inst_restr_to_given                   false
% 1.30/1.05  --inst_activity_threshold               500
% 1.30/1.05  --inst_out_proof                        true
% 1.30/1.05  
% 1.30/1.05  ------ Resolution Options
% 1.30/1.05  
% 1.30/1.05  --resolution_flag                       false
% 1.30/1.05  --res_lit_sel                           adaptive
% 1.30/1.05  --res_lit_sel_side                      none
% 1.30/1.05  --res_ordering                          kbo
% 1.30/1.05  --res_to_prop_solver                    active
% 1.30/1.05  --res_prop_simpl_new                    false
% 1.30/1.05  --res_prop_simpl_given                  true
% 1.30/1.05  --res_passive_queue_type                priority_queues
% 1.30/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.05  --res_passive_queues_freq               [15;5]
% 1.30/1.05  --res_forward_subs                      full
% 1.30/1.05  --res_backward_subs                     full
% 1.30/1.05  --res_forward_subs_resolution           true
% 1.30/1.05  --res_backward_subs_resolution          true
% 1.30/1.05  --res_orphan_elimination                true
% 1.30/1.05  --res_time_limit                        2.
% 1.30/1.05  --res_out_proof                         true
% 1.30/1.05  
% 1.30/1.05  ------ Superposition Options
% 1.30/1.05  
% 1.30/1.05  --superposition_flag                    true
% 1.30/1.05  --sup_passive_queue_type                priority_queues
% 1.30/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.05  --demod_completeness_check              fast
% 1.30/1.05  --demod_use_ground                      true
% 1.30/1.05  --sup_to_prop_solver                    passive
% 1.30/1.05  --sup_prop_simpl_new                    true
% 1.30/1.05  --sup_prop_simpl_given                  true
% 1.30/1.05  --sup_fun_splitting                     false
% 1.30/1.05  --sup_smt_interval                      50000
% 1.30/1.05  
% 1.30/1.05  ------ Superposition Simplification Setup
% 1.30/1.05  
% 1.30/1.05  --sup_indices_passive                   []
% 1.30/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_full_bw                           [BwDemod]
% 1.30/1.05  --sup_immed_triv                        [TrivRules]
% 1.30/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_immed_bw_main                     []
% 1.30/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.05  
% 1.30/1.05  ------ Combination Options
% 1.30/1.05  
% 1.30/1.05  --comb_res_mult                         3
% 1.30/1.05  --comb_sup_mult                         2
% 1.30/1.05  --comb_inst_mult                        10
% 1.30/1.05  
% 1.30/1.05  ------ Debug Options
% 1.30/1.05  
% 1.30/1.05  --dbg_backtrace                         false
% 1.30/1.05  --dbg_dump_prop_clauses                 false
% 1.30/1.05  --dbg_dump_prop_clauses_file            -
% 1.30/1.05  --dbg_out_stat                          false
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  ------ Proving...
% 1.30/1.05  
% 1.30/1.05  
% 1.30/1.05  % SZS status Theorem for theBenchmark.p
% 1.30/1.05  
% 1.30/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.30/1.05  
% 1.30/1.05  fof(f1,axiom,(
% 1.30/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.30/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.05  
% 1.30/1.05  fof(f11,plain,(
% 1.30/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.30/1.05    inference(pure_predicate_removal,[],[f1])).
% 1.30/1.05  
% 1.30/1.05  fof(f12,plain,(
% 1.30/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.30/1.05    inference(pure_predicate_removal,[],[f11])).
% 1.30/1.05  
% 1.30/1.05  fof(f13,plain,(
% 1.30/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.30/1.05    inference(pure_predicate_removal,[],[f12])).
% 1.30/1.05  
% 1.30/1.05  fof(f14,plain,(
% 1.30/1.05    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.30/1.05    inference(ennf_transformation,[],[f13])).
% 1.30/1.05  
% 1.30/1.05  fof(f15,plain,(
% 1.30/1.05    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.30/1.05    inference(flattening,[],[f14])).
% 1.30/1.05  
% 1.30/1.05  fof(f58,plain,(
% 1.30/1.05    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.30/1.05    inference(cnf_transformation,[],[f15])).
% 1.30/1.05  
% 1.30/1.05  fof(f2,axiom,(
% 1.30/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.30/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.05  
% 1.30/1.05  fof(f16,plain,(
% 1.30/1.05    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.05    inference(ennf_transformation,[],[f2])).
% 1.30/1.05  
% 1.30/1.05  fof(f17,plain,(
% 1.30/1.05    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(flattening,[],[f16])).
% 1.30/1.05  
% 1.30/1.05  fof(f32,plain,(
% 1.30/1.05    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(nnf_transformation,[],[f17])).
% 1.30/1.05  
% 1.30/1.05  fof(f60,plain,(
% 1.30/1.05    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.05    inference(cnf_transformation,[],[f32])).
% 1.30/1.05  
% 1.30/1.05  fof(f56,plain,(
% 1.30/1.05    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.30/1.05    inference(cnf_transformation,[],[f15])).
% 1.30/1.05  
% 1.30/1.05  fof(f57,plain,(
% 1.30/1.05    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.30/1.05    inference(cnf_transformation,[],[f15])).
% 1.30/1.05  
% 1.30/1.05  fof(f9,conjecture,(
% 1.30/1.05    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.30/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.05  
% 1.30/1.05  fof(f10,negated_conjecture,(
% 1.30/1.05    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.30/1.05    inference(negated_conjecture,[],[f9])).
% 1.30/1.05  
% 1.30/1.05  fof(f30,plain,(
% 1.30/1.05    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.30/1.05    inference(ennf_transformation,[],[f10])).
% 1.30/1.05  
% 1.30/1.05  fof(f31,plain,(
% 1.30/1.05    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.30/1.05    inference(flattening,[],[f30])).
% 1.30/1.05  
% 1.30/1.05  fof(f53,plain,(
% 1.30/1.05    ( ! [X0,X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,sK6))) & r2_hidden(X1,sK6))) )),
% 1.30/1.05    introduced(choice_axiom,[])).
% 1.30/1.05  
% 1.30/1.05  fof(f52,plain,(
% 1.30/1.05    ( ! [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),sK5) | ~r3_lattices(X0,sK5,k15_lattice3(X0,X2))) & r2_hidden(sK5,X2)) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.30/1.05    introduced(choice_axiom,[])).
% 1.30/1.05  
% 1.30/1.05  fof(f51,plain,(
% 1.30/1.05    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),X1) | ~r3_lattices(sK4,X1,k15_lattice3(sK4,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 1.30/1.05    introduced(choice_axiom,[])).
% 1.30/1.05  
% 1.30/1.05  fof(f54,plain,(
% 1.30/1.05    (((~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))) & r2_hidden(sK5,sK6)) & m1_subset_1(sK5,u1_struct_0(sK4))) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 1.30/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f53,f52,f51])).
% 1.30/1.05  
% 1.30/1.05  fof(f82,plain,(
% 1.30/1.05    v10_lattices(sK4)),
% 1.30/1.05    inference(cnf_transformation,[],[f54])).
% 1.30/1.05  
% 1.30/1.05  fof(f81,plain,(
% 1.30/1.05    ~v2_struct_0(sK4)),
% 1.30/1.05    inference(cnf_transformation,[],[f54])).
% 1.30/1.05  
% 1.30/1.05  fof(f84,plain,(
% 1.30/1.05    l3_lattices(sK4)),
% 1.30/1.05    inference(cnf_transformation,[],[f54])).
% 1.30/1.05  
% 1.30/1.05  fof(f4,axiom,(
% 1.30/1.05    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.30/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.05  
% 1.30/1.05  fof(f20,plain,(
% 1.30/1.05    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.05    inference(ennf_transformation,[],[f4])).
% 1.30/1.05  
% 1.30/1.05  fof(f21,plain,(
% 1.30/1.05    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(flattening,[],[f20])).
% 1.30/1.05  
% 1.30/1.05  fof(f37,plain,(
% 1.30/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(nnf_transformation,[],[f21])).
% 1.30/1.05  
% 1.30/1.05  fof(f38,plain,(
% 1.30/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(rectify,[],[f37])).
% 1.30/1.05  
% 1.30/1.05  fof(f39,plain,(
% 1.30/1.05    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.30/1.05    introduced(choice_axiom,[])).
% 1.30/1.05  
% 1.30/1.05  fof(f40,plain,(
% 1.30/1.05    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 1.30/1.05  
% 1.30/1.05  fof(f65,plain,(
% 1.30/1.05    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.05    inference(cnf_transformation,[],[f40])).
% 1.30/1.05  
% 1.30/1.05  fof(f3,axiom,(
% 1.30/1.05    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.30/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.06  
% 1.30/1.06  fof(f18,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.06    inference(ennf_transformation,[],[f3])).
% 1.30/1.06  
% 1.30/1.06  fof(f19,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f18])).
% 1.30/1.06  
% 1.30/1.06  fof(f33,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(nnf_transformation,[],[f19])).
% 1.30/1.06  
% 1.30/1.06  fof(f34,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(rectify,[],[f33])).
% 1.30/1.06  
% 1.30/1.06  fof(f35,plain,(
% 1.30/1.06    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.30/1.06    introduced(choice_axiom,[])).
% 1.30/1.06  
% 1.30/1.06  fof(f36,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 1.30/1.06  
% 1.30/1.06  fof(f61,plain,(
% 1.30/1.06    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(cnf_transformation,[],[f36])).
% 1.30/1.06  
% 1.30/1.06  fof(f6,axiom,(
% 1.30/1.06    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.30/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.06  
% 1.30/1.06  fof(f24,plain,(
% 1.30/1.06    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.06    inference(ennf_transformation,[],[f6])).
% 1.30/1.06  
% 1.30/1.06  fof(f25,plain,(
% 1.30/1.06    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f24])).
% 1.30/1.06  
% 1.30/1.06  fof(f74,plain,(
% 1.30/1.06    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(cnf_transformation,[],[f25])).
% 1.30/1.06  
% 1.30/1.06  fof(f7,axiom,(
% 1.30/1.06    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.30/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.06  
% 1.30/1.06  fof(f26,plain,(
% 1.30/1.06    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.06    inference(ennf_transformation,[],[f7])).
% 1.30/1.06  
% 1.30/1.06  fof(f27,plain,(
% 1.30/1.06    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f26])).
% 1.30/1.06  
% 1.30/1.06  fof(f75,plain,(
% 1.30/1.06    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(cnf_transformation,[],[f27])).
% 1.30/1.06  
% 1.30/1.06  fof(f8,axiom,(
% 1.30/1.06    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.30/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.06  
% 1.30/1.06  fof(f28,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.06    inference(ennf_transformation,[],[f8])).
% 1.30/1.06  
% 1.30/1.06  fof(f29,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f28])).
% 1.30/1.06  
% 1.30/1.06  fof(f46,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(nnf_transformation,[],[f29])).
% 1.30/1.06  
% 1.30/1.06  fof(f47,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f46])).
% 1.30/1.06  
% 1.30/1.06  fof(f48,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(rectify,[],[f47])).
% 1.30/1.06  
% 1.30/1.06  fof(f49,plain,(
% 1.30/1.06    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 1.30/1.06    introduced(choice_axiom,[])).
% 1.30/1.06  
% 1.30/1.06  fof(f50,plain,(
% 1.30/1.06    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 1.30/1.06  
% 1.30/1.06  fof(f76,plain,(
% 1.30/1.06    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(cnf_transformation,[],[f50])).
% 1.30/1.06  
% 1.30/1.06  fof(f91,plain,(
% 1.30/1.06    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(equality_resolution,[],[f76])).
% 1.30/1.06  
% 1.30/1.06  fof(f83,plain,(
% 1.30/1.06    v4_lattice3(sK4)),
% 1.30/1.06    inference(cnf_transformation,[],[f54])).
% 1.30/1.06  
% 1.30/1.06  fof(f5,axiom,(
% 1.30/1.06    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.30/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.30/1.06  
% 1.30/1.06  fof(f22,plain,(
% 1.30/1.06    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.30/1.06    inference(ennf_transformation,[],[f5])).
% 1.30/1.06  
% 1.30/1.06  fof(f23,plain,(
% 1.30/1.06    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f22])).
% 1.30/1.06  
% 1.30/1.06  fof(f41,plain,(
% 1.30/1.06    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(nnf_transformation,[],[f23])).
% 1.30/1.06  
% 1.30/1.06  fof(f42,plain,(
% 1.30/1.06    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(flattening,[],[f41])).
% 1.30/1.06  
% 1.30/1.06  fof(f43,plain,(
% 1.30/1.06    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(rectify,[],[f42])).
% 1.30/1.06  
% 1.30/1.06  fof(f44,plain,(
% 1.30/1.06    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.30/1.06    introduced(choice_axiom,[])).
% 1.30/1.06  
% 1.30/1.06  fof(f45,plain,(
% 1.30/1.06    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.30/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.30/1.06  
% 1.30/1.06  fof(f69,plain,(
% 1.30/1.06    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(cnf_transformation,[],[f45])).
% 1.30/1.06  
% 1.30/1.06  fof(f89,plain,(
% 1.30/1.06    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/1.06    inference(equality_resolution,[],[f69])).
% 1.30/1.06  
% 1.30/1.06  fof(f87,plain,(
% 1.30/1.06    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5) | ~r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))),
% 1.30/1.06    inference(cnf_transformation,[],[f54])).
% 1.30/1.06  
% 1.30/1.06  fof(f86,plain,(
% 1.30/1.06    r2_hidden(sK5,sK6)),
% 1.30/1.06    inference(cnf_transformation,[],[f54])).
% 1.30/1.06  
% 1.30/1.06  fof(f85,plain,(
% 1.30/1.06    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.30/1.06    inference(cnf_transformation,[],[f54])).
% 1.30/1.06  
% 1.30/1.06  cnf(c_0,plain,
% 1.30/1.06      ( ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0)
% 1.30/1.06      | v9_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f58]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_4,plain,
% 1.30/1.06      ( ~ r1_lattices(X0,X1,X2)
% 1.30/1.06      | r3_lattices(X0,X1,X2)
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ v6_lattices(X0)
% 1.30/1.06      | ~ v8_lattices(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v9_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f60]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_403,plain,
% 1.30/1.06      ( ~ r1_lattices(X0,X1,X2)
% 1.30/1.06      | r3_lattices(X0,X1,X2)
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ v6_lattices(X0)
% 1.30/1.06      | ~ v8_lattices(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2,plain,
% 1.30/1.06      ( v6_lattices(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f56]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1,plain,
% 1.30/1.06      ( v8_lattices(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f57]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_407,plain,
% 1.30/1.06      ( ~ r1_lattices(X0,X1,X2)
% 1.30/1.06      | r3_lattices(X0,X1,X2)
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_403,c_2,c_1]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_31,negated_conjecture,
% 1.30/1.06      ( v10_lattices(sK4) ),
% 1.30/1.06      inference(cnf_transformation,[],[f82]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_957,plain,
% 1.30/1.06      ( ~ r1_lattices(X0,X1,X2)
% 1.30/1.06      | r3_lattices(X0,X1,X2)
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_407,c_31]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_958,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,X0,X1)
% 1.30/1.06      | r3_lattices(sK4,X0,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.30/1.06      | ~ l3_lattices(sK4)
% 1.30/1.06      | v2_struct_0(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_957]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_32,negated_conjecture,
% 1.30/1.06      ( ~ v2_struct_0(sK4) ),
% 1.30/1.06      inference(cnf_transformation,[],[f81]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_29,negated_conjecture,
% 1.30/1.06      ( l3_lattices(sK4) ),
% 1.30/1.06      inference(cnf_transformation,[],[f84]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_962,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,X0,X1)
% 1.30/1.06      | r3_lattices(sK4,X0,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_958,c_32,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_963,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,X0,X1)
% 1.30/1.06      | r3_lattices(sK4,X0,X1)
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(renaming,[status(thm)],[c_962]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2502,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,X0_52,X1_52)
% 1.30/1.06      | r3_lattices(sK4,X0_52,X1_52)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_963]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3389,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
% 1.30/1.06      | r3_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2502]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3391,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.30/1.06      | r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.30/1.06      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_3389]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3371,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
% 1.30/1.06      | r3_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2502]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3373,plain,
% 1.30/1.06      ( ~ r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.30/1.06      | r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.30/1.06      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_3371]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_13,plain,
% 1.30/1.06      ( ~ r4_lattice3(X0,X1,X2)
% 1.30/1.06      | r1_lattices(X0,X3,X1)
% 1.30/1.06      | ~ r2_hidden(X3,X2)
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f65]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1045,plain,
% 1.30/1.06      ( ~ r4_lattice3(X0,X1,X2)
% 1.30/1.06      | r1_lattices(X0,X3,X1)
% 1.30/1.06      | ~ r2_hidden(X3,X2)
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1046,plain,
% 1.30/1.06      ( ~ r4_lattice3(sK4,X0,X1)
% 1.30/1.06      | r1_lattices(sK4,X2,X0)
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.30/1.06      | ~ l3_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_1045]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1050,plain,
% 1.30/1.06      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | r1_lattices(sK4,X2,X0)
% 1.30/1.06      | ~ r4_lattice3(sK4,X0,X1) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_1046,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1051,plain,
% 1.30/1.06      ( ~ r4_lattice3(sK4,X0,X1)
% 1.30/1.06      | r1_lattices(sK4,X2,X0)
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(renaming,[status(thm)],[c_1050]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2498,plain,
% 1.30/1.06      ( ~ r4_lattice3(sK4,X0_52,X0_53)
% 1.30/1.06      | r1_lattices(sK4,X1_52,X0_52)
% 1.30/1.06      | ~ r2_hidden(X1_52,X0_53)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_1051]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3253,plain,
% 1.30/1.06      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_53),X0_53)
% 1.30/1.06      | r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_53))
% 1.30/1.06      | ~ r2_hidden(X0_52,X0_53)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2498]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3255,plain,
% 1.30/1.06      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6)
% 1.30/1.06      | r1_lattices(sK4,sK5,k15_lattice3(sK4,sK6))
% 1.30/1.06      | ~ r2_hidden(sK5,sK6)
% 1.30/1.06      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_3253]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_9,plain,
% 1.30/1.06      ( ~ r3_lattice3(X0,X1,X2)
% 1.30/1.06      | r1_lattices(X0,X1,X3)
% 1.30/1.06      | ~ r2_hidden(X3,X2)
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f61]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1135,plain,
% 1.30/1.06      ( ~ r3_lattice3(X0,X1,X2)
% 1.30/1.06      | r1_lattices(X0,X1,X3)
% 1.30/1.06      | ~ r2_hidden(X3,X2)
% 1.30/1.06      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.30/1.06      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_32]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1136,plain,
% 1.30/1.06      ( ~ r3_lattice3(sK4,X0,X1)
% 1.30/1.06      | r1_lattices(sK4,X0,X2)
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.30/1.06      | ~ l3_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_1135]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1140,plain,
% 1.30/1.06      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | r1_lattices(sK4,X0,X2)
% 1.30/1.06      | ~ r3_lattice3(sK4,X0,X1) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_1136,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1141,plain,
% 1.30/1.06      ( ~ r3_lattice3(sK4,X0,X1)
% 1.30/1.06      | r1_lattices(sK4,X0,X2)
% 1.30/1.06      | ~ r2_hidden(X2,X1)
% 1.30/1.06      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(renaming,[status(thm)],[c_1140]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2494,plain,
% 1.30/1.06      ( ~ r3_lattice3(sK4,X0_52,X0_53)
% 1.30/1.06      | r1_lattices(sK4,X0_52,X1_52)
% 1.30/1.06      | ~ r2_hidden(X1_52,X0_53)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_1141]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3248,plain,
% 1.30/1.06      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,X0_53),X0_53)
% 1.30/1.06      | r1_lattices(sK4,k16_lattice3(sK4,X0_53),X0_52)
% 1.30/1.06      | ~ r2_hidden(X0_52,X0_53)
% 1.30/1.06      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2494]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_3250,plain,
% 1.30/1.06      ( ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6)
% 1.30/1.06      | r1_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.30/1.06      | ~ r2_hidden(sK5,sK6)
% 1.30/1.06      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4))
% 1.30/1.06      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_3248]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_19,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f74]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1030,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1031,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 1.30/1.06      | ~ l3_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_1030]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1035,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_1031,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2499,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_1035]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2568,plain,
% 1.30/1.06      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2499]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_20,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f75]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1015,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1016,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 1.30/1.06      | ~ l3_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_1015]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_1020,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_1016,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2500,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(sK4,X0_53),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_1020]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2565,plain,
% 1.30/1.06      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2500]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_25,plain,
% 1.30/1.06      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ v4_lattice3(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f91]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_190,plain,
% 1.30/1.06      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ v4_lattice3(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_25,c_20]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_30,negated_conjecture,
% 1.30/1.06      ( v4_lattice3(sK4) ),
% 1.30/1.06      inference(cnf_transformation,[],[f83]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_706,plain,
% 1.30/1.06      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_190,c_30]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_707,plain,
% 1.30/1.06      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
% 1.30/1.06      | ~ l3_lattices(sK4)
% 1.30/1.06      | v2_struct_0(sK4)
% 1.30/1.06      | ~ v10_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_706]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_711,plain,
% 1.30/1.06      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_707,c_32,c_31,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2509,plain,
% 1.30/1.06      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_53),X0_53) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_711]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2538,plain,
% 1.30/1.06      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK6) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2509]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_18,plain,
% 1.30/1.06      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 1.30/1.06      | ~ v4_lattice3(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(cnf_transformation,[],[f89]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_203,plain,
% 1.30/1.06      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ v4_lattice3(X0)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_18,c_19]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_691,plain,
% 1.30/1.06      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 1.30/1.06      | ~ l3_lattices(X0)
% 1.30/1.06      | v2_struct_0(X0)
% 1.30/1.06      | ~ v10_lattices(X0)
% 1.30/1.06      | sK4 != X0 ),
% 1.30/1.06      inference(resolution_lifted,[status(thm)],[c_203,c_30]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_692,plain,
% 1.30/1.06      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 1.30/1.06      | ~ l3_lattices(sK4)
% 1.30/1.06      | v2_struct_0(sK4)
% 1.30/1.06      | ~ v10_lattices(sK4) ),
% 1.30/1.06      inference(unflattening,[status(thm)],[c_691]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_696,plain,
% 1.30/1.06      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 1.30/1.06      inference(global_propositional_subsumption,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_692,c_32,c_31,c_29]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2510,plain,
% 1.30/1.06      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_53),X0_53) ),
% 1.30/1.06      inference(subtyping,[status(esa)],[c_696]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_2535,plain,
% 1.30/1.06      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK6) ),
% 1.30/1.06      inference(instantiation,[status(thm)],[c_2510]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_26,negated_conjecture,
% 1.30/1.06      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),sK5)
% 1.30/1.06      | ~ r3_lattices(sK4,sK5,k15_lattice3(sK4,sK6)) ),
% 1.30/1.06      inference(cnf_transformation,[],[f87]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_27,negated_conjecture,
% 1.30/1.06      ( r2_hidden(sK5,sK6) ),
% 1.30/1.06      inference(cnf_transformation,[],[f86]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(c_28,negated_conjecture,
% 1.30/1.06      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.30/1.06      inference(cnf_transformation,[],[f85]) ).
% 1.30/1.06  
% 1.30/1.06  cnf(contradiction,plain,
% 1.30/1.06      ( $false ),
% 1.30/1.06      inference(minisat,
% 1.30/1.06                [status(thm)],
% 1.30/1.06                [c_3391,c_3373,c_3255,c_3250,c_2568,c_2565,c_2538,c_2535,
% 1.30/1.06                 c_26,c_27,c_28]) ).
% 1.30/1.06  
% 1.30/1.06  
% 1.30/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.30/1.06  
% 1.30/1.06  ------                               Statistics
% 1.30/1.06  
% 1.30/1.06  ------ General
% 1.30/1.06  
% 1.30/1.06  abstr_ref_over_cycles:                  0
% 1.30/1.06  abstr_ref_under_cycles:                 0
% 1.30/1.06  gc_basic_clause_elim:                   0
% 1.30/1.06  forced_gc_time:                         0
% 1.30/1.06  parsing_time:                           0.019
% 1.30/1.06  unif_index_cands_time:                  0.
% 1.30/1.06  unif_index_add_time:                    0.
% 1.30/1.06  orderings_time:                         0.
% 1.30/1.06  out_proof_time:                         0.009
% 1.30/1.06  total_time:                             0.17
% 1.30/1.06  num_of_symbols:                         55
% 1.30/1.06  num_of_terms:                           2293
% 1.30/1.06  
% 1.30/1.06  ------ Preprocessing
% 1.30/1.06  
% 1.30/1.06  num_of_splits:                          0
% 1.30/1.06  num_of_split_atoms:                     0
% 1.30/1.06  num_of_reused_defs:                     0
% 1.30/1.06  num_eq_ax_congr_red:                    55
% 1.30/1.06  num_of_sem_filtered_clauses:            1
% 1.30/1.06  num_of_subtypes:                        4
% 1.30/1.06  monotx_restored_types:                  0
% 1.30/1.06  sat_num_of_epr_types:                   0
% 1.30/1.06  sat_num_of_non_cyclic_types:            0
% 1.30/1.06  sat_guarded_non_collapsed_types:        1
% 1.30/1.06  num_pure_diseq_elim:                    0
% 1.30/1.06  simp_replaced_by:                       0
% 1.30/1.06  res_preprocessed:                       124
% 1.30/1.06  prep_upred:                             0
% 1.30/1.06  prep_unflattend:                        116
% 1.30/1.06  smt_new_axioms:                         0
% 1.30/1.06  pred_elim_cands:                        6
% 1.30/1.06  pred_elim:                              7
% 1.30/1.06  pred_elim_cl:                           7
% 1.30/1.06  pred_elim_cycles:                       12
% 1.30/1.06  merged_defs:                            0
% 1.30/1.06  merged_defs_ncl:                        0
% 1.30/1.06  bin_hyper_res:                          0
% 1.30/1.06  prep_cycles:                            4
% 1.30/1.06  pred_elim_time:                         0.06
% 1.30/1.06  splitting_time:                         0.
% 1.30/1.06  sem_filter_time:                        0.
% 1.30/1.06  monotx_time:                            0.
% 1.30/1.06  subtype_inf_time:                       0.
% 1.30/1.06  
% 1.30/1.06  ------ Problem properties
% 1.30/1.06  
% 1.30/1.06  clauses:                                25
% 1.30/1.06  conjectures:                            3
% 1.30/1.06  epr:                                    1
% 1.30/1.06  horn:                                   17
% 1.30/1.06  ground:                                 3
% 1.30/1.06  unary:                                  6
% 1.30/1.06  binary:                                 1
% 1.30/1.06  lits:                                   74
% 1.30/1.06  lits_eq:                                6
% 1.30/1.06  fd_pure:                                0
% 1.30/1.06  fd_pseudo:                              0
% 1.30/1.06  fd_cond:                                0
% 1.30/1.06  fd_pseudo_cond:                         6
% 1.30/1.06  ac_symbols:                             0
% 1.30/1.06  
% 1.30/1.06  ------ Propositional Solver
% 1.30/1.06  
% 1.30/1.06  prop_solver_calls:                      23
% 1.30/1.06  prop_fast_solver_calls:                 1482
% 1.30/1.06  smt_solver_calls:                       0
% 1.30/1.06  smt_fast_solver_calls:                  0
% 1.30/1.06  prop_num_of_clauses:                    686
% 1.30/1.06  prop_preprocess_simplified:             4125
% 1.30/1.06  prop_fo_subsumed:                       80
% 1.30/1.06  prop_solver_time:                       0.
% 1.30/1.06  smt_solver_time:                        0.
% 1.30/1.06  smt_fast_solver_time:                   0.
% 1.30/1.06  prop_fast_solver_time:                  0.
% 1.30/1.06  prop_unsat_core_time:                   0.
% 1.30/1.06  
% 1.30/1.06  ------ QBF
% 1.30/1.06  
% 1.30/1.06  qbf_q_res:                              0
% 1.30/1.06  qbf_num_tautologies:                    0
% 1.30/1.06  qbf_prep_cycles:                        0
% 1.30/1.06  
% 1.30/1.06  ------ BMC1
% 1.30/1.06  
% 1.30/1.06  bmc1_current_bound:                     -1
% 1.30/1.06  bmc1_last_solved_bound:                 -1
% 1.30/1.06  bmc1_unsat_core_size:                   -1
% 1.30/1.06  bmc1_unsat_core_parents_size:           -1
% 1.30/1.06  bmc1_merge_next_fun:                    0
% 1.30/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.30/1.06  
% 1.30/1.06  ------ Instantiation
% 1.30/1.06  
% 1.30/1.06  inst_num_of_clauses:                    63
% 1.30/1.06  inst_num_in_passive:                    4
% 1.30/1.06  inst_num_in_active:                     45
% 1.30/1.06  inst_num_in_unprocessed:                13
% 1.30/1.06  inst_num_of_loops:                      47
% 1.30/1.06  inst_num_of_learning_restarts:          0
% 1.30/1.06  inst_num_moves_active_passive:          0
% 1.30/1.06  inst_lit_activity:                      0
% 1.30/1.06  inst_lit_activity_moves:                0
% 1.30/1.06  inst_num_tautologies:                   0
% 1.30/1.06  inst_num_prop_implied:                  0
% 1.30/1.06  inst_num_existing_simplified:           0
% 1.30/1.06  inst_num_eq_res_simplified:             0
% 1.30/1.06  inst_num_child_elim:                    0
% 1.30/1.06  inst_num_of_dismatching_blockings:      0
% 1.30/1.06  inst_num_of_non_proper_insts:           33
% 1.30/1.06  inst_num_of_duplicates:                 0
% 1.30/1.06  inst_inst_num_from_inst_to_res:         0
% 1.30/1.06  inst_dismatching_checking_time:         0.
% 1.30/1.06  
% 1.30/1.06  ------ Resolution
% 1.30/1.06  
% 1.30/1.06  res_num_of_clauses:                     0
% 1.30/1.06  res_num_in_passive:                     0
% 1.30/1.06  res_num_in_active:                      0
% 1.30/1.06  res_num_of_loops:                       128
% 1.30/1.06  res_forward_subset_subsumed:            4
% 1.30/1.06  res_backward_subset_subsumed:           0
% 1.30/1.06  res_forward_subsumed:                   0
% 1.30/1.06  res_backward_subsumed:                  0
% 1.30/1.06  res_forward_subsumption_resolution:     8
% 1.30/1.06  res_backward_subsumption_resolution:    2
% 1.30/1.06  res_clause_to_clause_subsumption:       135
% 1.30/1.06  res_orphan_elimination:                 0
% 1.30/1.06  res_tautology_del:                      3
% 1.30/1.06  res_num_eq_res_simplified:              0
% 1.30/1.06  res_num_sel_changes:                    0
% 1.30/1.06  res_moves_from_active_to_pass:          0
% 1.30/1.06  
% 1.30/1.06  ------ Superposition
% 1.30/1.06  
% 1.30/1.06  sup_time_total:                         0.
% 1.30/1.06  sup_time_generating:                    0.
% 1.30/1.06  sup_time_sim_full:                      0.
% 1.30/1.06  sup_time_sim_immed:                     0.
% 1.30/1.06  
% 1.30/1.06  sup_num_of_clauses:                     25
% 1.30/1.06  sup_num_in_active:                      8
% 1.30/1.06  sup_num_in_passive:                     17
% 1.30/1.06  sup_num_of_loops:                       8
% 1.30/1.06  sup_fw_superposition:                   0
% 1.30/1.06  sup_bw_superposition:                   0
% 1.30/1.06  sup_immediate_simplified:               0
% 1.30/1.06  sup_given_eliminated:                   0
% 1.30/1.06  comparisons_done:                       0
% 1.30/1.06  comparisons_avoided:                    0
% 1.30/1.06  
% 1.30/1.06  ------ Simplifications
% 1.30/1.06  
% 1.30/1.06  
% 1.30/1.06  sim_fw_subset_subsumed:                 0
% 1.30/1.06  sim_bw_subset_subsumed:                 0
% 1.30/1.06  sim_fw_subsumed:                        0
% 1.30/1.06  sim_bw_subsumed:                        0
% 1.30/1.06  sim_fw_subsumption_res:                 0
% 1.30/1.06  sim_bw_subsumption_res:                 0
% 1.30/1.06  sim_tautology_del:                      0
% 1.30/1.06  sim_eq_tautology_del:                   0
% 1.30/1.06  sim_eq_res_simp:                        0
% 1.30/1.06  sim_fw_demodulated:                     0
% 1.30/1.06  sim_bw_demodulated:                     0
% 1.30/1.06  sim_light_normalised:                   0
% 1.30/1.06  sim_joinable_taut:                      0
% 1.30/1.06  sim_joinable_simp:                      0
% 1.30/1.06  sim_ac_normalised:                      0
% 1.30/1.06  sim_smt_subsumption:                    0
% 1.30/1.06  
%------------------------------------------------------------------------------
