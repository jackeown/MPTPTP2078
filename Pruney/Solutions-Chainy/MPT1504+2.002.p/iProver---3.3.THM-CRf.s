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
% DateTime   : Thu Dec  3 12:19:09 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 781 expanded)
%              Number of clauses        :  128 ( 194 expanded)
%              Number of leaves         :   17 ( 201 expanded)
%              Depth                    :   22
%              Number of atoms          : 1132 (4098 expanded)
%              Number of equality atoms :  118 ( 674 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(nnf_transformation,[],[f26])).

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
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
     => k15_lattice3(X0,sK5) != k16_lattice3(X0,a_2_2_lattice3(X0,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK4,X1) != k16_lattice3(sK4,a_2_2_lattice3(sK4,X1))
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5))
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f49,f48])).

fof(f78,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f54,plain,(
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

fof(f56,plain,(
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

fof(f52,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
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

fof(f81,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f58,plain,(
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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f61,plain,(
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

fof(f82,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f80,plain,(
    k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_967,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_968,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_29,c_28,c_26])).

cnf(c_973,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_972])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_359,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_363,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_2,c_1])).

cnf(c_1220,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_28])).

cnf(c_1221,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1225,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_29,c_26])).

cnf(c_1226,plain,
    ( ~ r1_lattices(sK4,X0,X1)
    | r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1225])).

cnf(c_1449,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | X3 != X0
    | sK3(sK4,X0,X1) != X2
    | k16_lattice3(sK4,X1) = X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_973,c_1226])).

cnf(c_1450,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1449])).

cnf(c_22,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_919,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_920,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_919])).

cnf(c_924,plain,
    ( m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_920,c_29,c_28,c_26])).

cnf(c_925,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_924])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1450,c_925])).

cnf(c_1455,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_1454])).

cnf(c_2357,plain,
    ( ~ r3_lattice3(sK4,X0_52,X0_53)
    | ~ r1_lattices(sK4,sK3(sK4,X0_52,X0_53),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_1455])).

cnf(c_3131,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
    | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),k15_lattice3(sK4,X0_55))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_11666,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
    | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55)),k15_lattice3(sK4,X0_55))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_3131])).

cnf(c_11668,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),k15_lattice3(sK4,sK5))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_11666])).

cnf(c_6,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1362,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_1363,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_26])).

cnf(c_1368,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1367])).

cnf(c_2361,plain,
    ( r3_lattice3(sK4,X0_52,X0_53)
    | ~ r1_lattices(sK4,X0_52,sK0(sK4,X0_52,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1368])).

cnf(c_15,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1278,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_1279,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1278])).

cnf(c_1283,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1279,c_26])).

cnf(c_13,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1030,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_1031,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_29,c_28,c_26])).

cnf(c_1036,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1035])).

cnf(c_1384,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1283,c_1036])).

cnf(c_2360,plain,
    ( ~ r4_lattice3(sK4,X0_52,X0_55)
    | r1_lattices(sK4,k15_lattice3(sK4,X0_55),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1384])).

cnf(c_3945,plain,
    ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_55)
    | r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
    | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_2361,c_2360])).

cnf(c_2365,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1283])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1320,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_1321,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1320])).

cnf(c_1325,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_26])).

cnf(c_1326,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1325])).

cnf(c_2363,plain,
    ( r3_lattice3(sK4,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_52,X0_53),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1326])).

cnf(c_3014,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_4882,plain,
    ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_55)
    | r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3945,c_2365,c_3014])).

cnf(c_2380,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_2379,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_3525,plain,
    ( X0_52 != X1_52
    | X1_52 = X0_52 ),
    inference(resolution,[status(thm)],[c_2380,c_2379])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1144,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_1145,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_1144])).

cnf(c_1149,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_29,c_28,c_26])).

cnf(c_2366,plain,
    ( ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
    | sK2(X0_52,sK4,X0_55) = X0_52 ),
    inference(subtyping,[status(esa)],[c_1149])).

cnf(c_4414,plain,
    ( ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
    | X0_52 = sK2(X0_52,sK4,X0_55) ),
    inference(resolution,[status(thm)],[c_3525,c_2366])).

cnf(c_2385,plain,
    ( ~ r4_lattice3(X0_51,X0_52,X0_55)
    | r4_lattice3(X0_51,X1_52,X0_55)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_4580,plain,
    ( r4_lattice3(X0_51,X0_52,X0_55)
    | ~ r4_lattice3(X0_51,sK2(X0_52,sK4,X1_55),X0_55)
    | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X1_55)) ),
    inference(resolution,[status(thm)],[c_4414,c_2385])).

cnf(c_17,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_991,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_992,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_996,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_992,c_29,c_28,c_26])).

cnf(c_997,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_996])).

cnf(c_2372,plain,
    ( r4_lattice3(sK4,sK2(X0_52,sK4,X0_55),X0_55)
    | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55)) ),
    inference(subtyping,[status(esa)],[c_997])).

cnf(c_7108,plain,
    ( r4_lattice3(sK4,X0_52,X0_55)
    | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55)) ),
    inference(resolution,[status(thm)],[c_4580,c_2372])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1341,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_1342,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1341])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1342,c_26])).

cnf(c_1347,plain,
    ( r3_lattice3(sK4,X0,X1)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1346])).

cnf(c_2362,plain,
    ( r3_lattice3(sK4,X0_52,X0_53)
    | r2_hidden(sK0(sK4,X0_52,X0_53),X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1347])).

cnf(c_7539,plain,
    ( r4_lattice3(sK4,sK0(sK4,X0_52,a_2_2_lattice3(sK4,X0_55)),X0_55)
    | r3_lattice3(sK4,X0_52,a_2_2_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_7108,c_2362])).

cnf(c_7683,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_4882,c_7539])).

cnf(c_7685,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7683])).

cnf(c_9,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1293,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_1294,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_26])).

cnf(c_1299,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1298])).

cnf(c_2364,plain,
    ( ~ r3_lattice3(sK4,X0_52,X0_53)
    | r1_lattices(sK4,X0_52,X1_52)
    | ~ r2_hidden(X1_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1299])).

cnf(c_3156,plain,
    ( ~ r3_lattice3(sK4,X0_52,a_2_2_lattice3(sK4,X0_55))
    | r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_55))
    | ~ r2_hidden(k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_4349,plain,
    ( ~ r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),a_2_2_lattice3(sK4,X1_55))
    | r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),k15_lattice3(sK4,X1_55))
    | ~ r2_hidden(k15_lattice3(sK4,X1_55),a_2_2_lattice3(sK4,X1_55))
    | ~ m1_subset_1(sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X1_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_4353,plain,
    ( ~ r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),a_2_2_lattice3(sK4,sK5))
    | r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),k15_lattice3(sK4,sK5))
    | ~ r2_hidden(k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | ~ m1_subset_1(sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4349])).

cnf(c_21,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_943,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattice3(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,X2) = X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_944,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ r3_lattice3(sK4,X0,X1)
    | k16_lattice3(sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_29,c_28,c_26])).

cnf(c_949,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k16_lattice3(sK4,X1) = X0 ),
    inference(renaming,[status(thm)],[c_948])).

cnf(c_2373,plain,
    ( ~ r3_lattice3(sK4,X0_52,X0_53)
    | r3_lattice3(sK4,sK3(sK4,X0_52,X0_53),X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_3133,plain,
    ( r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_53)
    | ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_3695,plain,
    ( r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),a_2_2_lattice3(sK4,sK5))
    | ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_2374,plain,
    ( ~ r3_lattice3(sK4,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0_52,X0_53),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_925])).

cnf(c_3134,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
    | m1_subset_1(sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
    | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_3641,plain,
    ( ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | m1_subset_1(sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3134])).

cnf(c_3126,plain,
    ( k15_lattice3(sK4,sK5) = k15_lattice3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_3089,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) != X0_52
    | k15_lattice3(sK4,sK5) != X0_52
    | k15_lattice3(sK4,sK5) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_3125,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) != k15_lattice3(sK4,sK5)
    | k15_lattice3(sK4,sK5) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5))
    | k15_lattice3(sK4,sK5) != k15_lattice3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3089])).

cnf(c_16,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1009,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_1010,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_29,c_28,c_26])).

cnf(c_1015,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1014])).

cnf(c_2371,plain,
    ( ~ r4_lattice3(sK4,X0_52,X0_55)
    | r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1015])).

cnf(c_3019,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55)
    | r2_hidden(k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_3021,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK5),sK5)
    | r2_hidden(k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
    | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3019])).

cnf(c_2429,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2365])).

cnf(c_14,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_180,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_862,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_27])).

cnf(c_863,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_867,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_863,c_29,c_28,c_26])).

cnf(c_2376,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_867])).

cnf(c_2396,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2376])).

cnf(c_25,negated_conjecture,
    ( k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2377,negated_conjecture,
    ( k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11668,c_7685,c_4353,c_3695,c_3641,c_3126,c_3125,c_3021,c_2429,c_2396,c_2377])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 3.66/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/0.97  
% 3.66/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/0.97  
% 3.66/0.97  ------  iProver source info
% 3.66/0.97  
% 3.66/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.66/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/0.97  git: non_committed_changes: false
% 3.66/0.97  git: last_make_outside_of_git: false
% 3.66/0.97  
% 3.66/0.97  ------ 
% 3.66/0.97  ------ Parsing...
% 3.66/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/0.97  
% 3.66/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.66/0.97  
% 3.66/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/0.97  
% 3.66/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/0.97  ------ Proving...
% 3.66/0.97  ------ Problem Properties 
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  clauses                                 21
% 3.66/0.97  conjectures                             1
% 3.66/0.97  EPR                                     0
% 3.66/0.97  Horn                                    15
% 3.66/0.97  unary                                   3
% 3.66/0.97  binary                                  4
% 3.66/0.97  lits                                    63
% 3.66/0.97  lits eq                                 9
% 3.66/0.97  fd_pure                                 0
% 3.66/0.97  fd_pseudo                               0
% 3.66/0.97  fd_cond                                 0
% 3.66/0.97  fd_pseudo_cond                          6
% 3.66/0.97  AC symbols                              0
% 3.66/0.97  
% 3.66/0.97  ------ Input Options Time Limit: Unbounded
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  ------ 
% 3.66/0.97  Current options:
% 3.66/0.97  ------ 
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  ------ Proving...
% 3.66/0.97  
% 3.66/0.97  
% 3.66/0.97  % SZS status Theorem for theBenchmark.p
% 3.66/0.97  
% 3.66/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/0.97  
% 3.66/0.97  fof(f7,axiom,(
% 3.66/0.97    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.66/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.97  
% 3.66/0.97  fof(f25,plain,(
% 3.66/0.97    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f7])).
% 3.66/0.98  
% 3.66/0.98  fof(f26,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f25])).
% 3.66/0.98  
% 3.66/0.98  fof(f43,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f26])).
% 3.66/0.98  
% 3.66/0.98  fof(f44,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f43])).
% 3.66/0.98  
% 3.66/0.98  fof(f45,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(rectify,[],[f44])).
% 3.66/0.98  
% 3.66/0.98  fof(f46,plain,(
% 3.66/0.98    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f47,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 3.66/0.98  
% 3.66/0.98  fof(f75,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | ~r3_lattices(X0,sK3(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f47])).
% 3.66/0.98  
% 3.66/0.98  fof(f8,conjecture,(
% 3.66/0.98    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f9,negated_conjecture,(
% 3.66/0.98    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.66/0.98    inference(negated_conjecture,[],[f8])).
% 3.66/0.98  
% 3.66/0.98  fof(f27,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f9])).
% 3.66/0.98  
% 3.66/0.98  fof(f28,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f27])).
% 3.66/0.98  
% 3.66/0.98  fof(f49,plain,(
% 3.66/0.98    ( ! [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) => k15_lattice3(X0,sK5) != k16_lattice3(X0,a_2_2_lattice3(X0,sK5))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f48,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK4,X1) != k16_lattice3(sK4,a_2_2_lattice3(sK4,X1)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f50,plain,(
% 3.66/0.98    k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f49,f48])).
% 3.66/0.98  
% 3.66/0.98  fof(f78,plain,(
% 3.66/0.98    v4_lattice3(sK4)),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  fof(f76,plain,(
% 3.66/0.98    ~v2_struct_0(sK4)),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  fof(f77,plain,(
% 3.66/0.98    v10_lattices(sK4)),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  fof(f79,plain,(
% 3.66/0.98    l3_lattices(sK4)),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  fof(f1,axiom,(
% 3.66/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f10,plain,(
% 3.66/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.66/0.98    inference(pure_predicate_removal,[],[f1])).
% 3.66/0.98  
% 3.66/0.98  fof(f11,plain,(
% 3.66/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.66/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.66/0.98  
% 3.66/0.98  fof(f12,plain,(
% 3.66/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.66/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.66/0.98  
% 3.66/0.98  fof(f13,plain,(
% 3.66/0.98    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f12])).
% 3.66/0.98  
% 3.66/0.98  fof(f14,plain,(
% 3.66/0.98    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.66/0.98    inference(flattening,[],[f13])).
% 3.66/0.98  
% 3.66/0.98  fof(f54,plain,(
% 3.66/0.98    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f14])).
% 3.66/0.98  
% 3.66/0.98  fof(f2,axiom,(
% 3.66/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f15,plain,(
% 3.66/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f2])).
% 3.66/0.98  
% 3.66/0.98  fof(f16,plain,(
% 3.66/0.98    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f15])).
% 3.66/0.98  
% 3.66/0.98  fof(f29,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f16])).
% 3.66/0.98  
% 3.66/0.98  fof(f56,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f29])).
% 3.66/0.98  
% 3.66/0.98  fof(f52,plain,(
% 3.66/0.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f14])).
% 3.66/0.98  
% 3.66/0.98  fof(f53,plain,(
% 3.66/0.98    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f14])).
% 3.66/0.98  
% 3.66/0.98  fof(f73,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f47])).
% 3.66/0.98  
% 3.66/0.98  fof(f3,axiom,(
% 3.66/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f17,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f3])).
% 3.66/0.98  
% 3.66/0.98  fof(f18,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f17])).
% 3.66/0.98  
% 3.66/0.98  fof(f30,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f18])).
% 3.66/0.98  
% 3.66/0.98  fof(f31,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(rectify,[],[f30])).
% 3.66/0.98  
% 3.66/0.98  fof(f32,plain,(
% 3.66/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f33,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.66/0.98  
% 3.66/0.98  fof(f60,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f33])).
% 3.66/0.98  
% 3.66/0.98  fof(f5,axiom,(
% 3.66/0.98    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f21,plain,(
% 3.66/0.98    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f5])).
% 3.66/0.98  
% 3.66/0.98  fof(f22,plain,(
% 3.66/0.98    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f21])).
% 3.66/0.98  
% 3.66/0.98  fof(f66,plain,(
% 3.66/0.98    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f22])).
% 3.66/0.98  
% 3.66/0.98  fof(f4,axiom,(
% 3.66/0.98    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f19,plain,(
% 3.66/0.98    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f4])).
% 3.66/0.98  
% 3.66/0.98  fof(f20,plain,(
% 3.66/0.98    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f19])).
% 3.66/0.98  
% 3.66/0.98  fof(f34,plain,(
% 3.66/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f20])).
% 3.66/0.98  
% 3.66/0.98  fof(f35,plain,(
% 3.66/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f36,plain,(
% 3.66/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(rectify,[],[f35])).
% 3.66/0.98  
% 3.66/0.98  fof(f37,plain,(
% 3.66/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f38,plain,(
% 3.66/0.98    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 3.66/0.98  
% 3.66/0.98  fof(f62,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f38])).
% 3.66/0.98  
% 3.66/0.98  fof(f81,plain,(
% 3.66/0.98    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(equality_resolution,[],[f62])).
% 3.66/0.98  
% 3.66/0.98  fof(f58,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f33])).
% 3.66/0.98  
% 3.66/0.98  fof(f6,axiom,(
% 3.66/0.98    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f23,plain,(
% 3.66/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.66/0.98    inference(ennf_transformation,[],[f6])).
% 3.66/0.98  
% 3.66/0.98  fof(f24,plain,(
% 3.66/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.66/0.98    inference(flattening,[],[f23])).
% 3.66/0.98  
% 3.66/0.98  fof(f39,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.66/0.98    inference(nnf_transformation,[],[f24])).
% 3.66/0.98  
% 3.66/0.98  fof(f40,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.66/0.98    inference(rectify,[],[f39])).
% 3.66/0.98  
% 3.66/0.98  fof(f41,plain,(
% 3.66/0.98    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f42,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 3.66/0.98  
% 3.66/0.98  fof(f68,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f42])).
% 3.66/0.98  
% 3.66/0.98  fof(f69,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK2(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f42])).
% 3.66/0.98  
% 3.66/0.98  fof(f59,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f33])).
% 3.66/0.98  
% 3.66/0.98  fof(f57,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f33])).
% 3.66/0.98  
% 3.66/0.98  fof(f74,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k16_lattice3(X0,X2) = X1 | r3_lattice3(X0,sK3(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f47])).
% 3.66/0.98  
% 3.66/0.98  fof(f70,plain,(
% 3.66/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f42])).
% 3.66/0.98  
% 3.66/0.98  fof(f83,plain,(
% 3.66/0.98    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.66/0.98    inference(equality_resolution,[],[f70])).
% 3.66/0.98  
% 3.66/0.98  fof(f61,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f38])).
% 3.66/0.98  
% 3.66/0.98  fof(f82,plain,(
% 3.66/0.98    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(equality_resolution,[],[f61])).
% 3.66/0.98  
% 3.66/0.98  fof(f80,plain,(
% 3.66/0.98    k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5))),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  cnf(c_20,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.66/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_27,negated_conjecture,
% 3.66/0.98      ( v4_lattice3(sK4) ),
% 3.66/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_967,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_968,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_967]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_29,negated_conjecture,
% 3.66/0.98      ( ~ v2_struct_0(sK4) ),
% 3.66/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_28,negated_conjecture,
% 3.66/0.98      ( v10_lattices(sK4) ),
% 3.66/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_26,negated_conjecture,
% 3.66/0.98      ( l3_lattices(sK4) ),
% 3.66/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_972,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_968,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_973,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r3_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_972]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_0,plain,
% 3.66/0.98      ( ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | v9_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4,plain,
% 3.66/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.66/0.98      | r3_lattices(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ v6_lattices(X0)
% 3.66/0.98      | ~ v8_lattices(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v9_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_359,plain,
% 3.66/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.66/0.98      | r3_lattices(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ v6_lattices(X0)
% 3.66/0.98      | ~ v8_lattices(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2,plain,
% 3.66/0.98      ( v6_lattices(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1,plain,
% 3.66/0.98      ( v8_lattices(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_363,plain,
% 3.66/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.66/0.98      | r3_lattices(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_359,c_2,c_1]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1220,plain,
% 3.66/0.98      ( ~ r1_lattices(X0,X1,X2)
% 3.66/0.98      | r3_lattices(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_363,c_28]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1221,plain,
% 3.66/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.66/0.98      | r3_lattices(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1220]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1225,plain,
% 3.66/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.66/0.98      | r3_lattices(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1221,c_29,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1226,plain,
% 3.66/0.98      ( ~ r1_lattices(sK4,X0,X1)
% 3.66/0.98      | r3_lattices(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1225]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1449,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r1_lattices(sK4,X2,X3)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 3.66/0.98      | X3 != X0
% 3.66/0.98      | sK3(sK4,X0,X1) != X2
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0
% 3.66/0.98      | sK4 != sK4 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_973,c_1226]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1450,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1449]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_22,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.66/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_919,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_920,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_919]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_924,plain,
% 3.66/0.98      ( m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_920,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_925,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_924]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1454,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1450,c_925]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1455,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,X0,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1454]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2357,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,X0_52,X0_53),X0_52)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = X0_52 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1455]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3131,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),k15_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2357]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_11666,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55)),k15_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3131]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_11668,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),k15_lattice3(sK4,sK5))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_11666]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_6,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1362,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1363,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1362]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1367,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.66/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1363,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1368,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1367]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2361,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | ~ r1_lattices(sK4,X0_52,sK0(sK4,X0_52,X0_53))
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1368]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_15,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1278,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1279,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1278]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1283,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1279,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_13,plain,
% 3.66/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.66/0.98      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1030,plain,
% 3.66/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.66/0.98      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1031,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.66/0.98      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1030]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1035,plain,
% 3.66/0.98      ( ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.66/0.98      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1031,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1036,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.66/0.98      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1035]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1384,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.66/0.98      | r1_lattices(sK4,k15_lattice3(sK4,X1),X0)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(backward_subsumption_resolution,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1283,c_1036]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2360,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0_52,X0_55)
% 3.66/0.98      | r1_lattices(sK4,k15_lattice3(sK4,X0_55),X0_52)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1384]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3945,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_55)
% 3.66/0.98      | r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
% 3.66/0.98      | ~ m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_2361,c_2360]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2365,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1283]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1320,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1321,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1320]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1325,plain,
% 3.66/0.98      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1321,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1326,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1325]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2363,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK0(sK4,X0_52,X0_53),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1326]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3014,plain,
% 3.66/0.98      ( r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
% 3.66/0.98      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4882,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_55)
% 3.66/0.98      | r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_3945,c_2365,c_3014]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2380,plain,
% 3.66/0.98      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 3.66/0.98      theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2379,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3525,plain,
% 3.66/0.98      ( X0_52 != X1_52 | X1_52 = X0_52 ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_2380,c_2379]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_18,plain,
% 3.66/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.66/0.98      | ~ v4_lattice3(X1)
% 3.66/0.98      | ~ l3_lattices(X1)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | ~ v10_lattices(X1)
% 3.66/0.98      | sK2(X0,X1,X2) = X0 ),
% 3.66/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1144,plain,
% 3.66/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.66/0.98      | ~ l3_lattices(X1)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | ~ v10_lattices(X1)
% 3.66/0.98      | sK2(X0,X1,X2) = X0
% 3.66/0.98      | sK4 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1145,plain,
% 3.66/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4)
% 3.66/0.98      | sK2(X0,sK4,X1) = X0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1144]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1149,plain,
% 3.66/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) | sK2(X0,sK4,X1) = X0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1145,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2366,plain,
% 3.66/0.98      ( ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | sK2(X0_52,sK4,X0_55) = X0_52 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1149]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4414,plain,
% 3.66/0.98      ( ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | X0_52 = sK2(X0_52,sK4,X0_55) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_3525,c_2366]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2385,plain,
% 3.66/0.98      ( ~ r4_lattice3(X0_51,X0_52,X0_55)
% 3.66/0.98      | r4_lattice3(X0_51,X1_52,X0_55)
% 3.66/0.98      | X1_52 != X0_52 ),
% 3.66/0.98      theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4580,plain,
% 3.66/0.98      ( r4_lattice3(X0_51,X0_52,X0_55)
% 3.66/0.98      | ~ r4_lattice3(X0_51,sK2(X0_52,sK4,X1_55),X0_55)
% 3.66/0.98      | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X1_55)) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_4414,c_2385]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_17,plain,
% 3.66/0.98      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.66/0.98      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_991,plain,
% 3.66/0.98      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.66/0.98      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_992,plain,
% 3.66/0.98      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.66/0.98      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_991]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_996,plain,
% 3.66/0.98      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_992,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_997,plain,
% 3.66/0.98      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.66/0.98      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_996]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2372,plain,
% 3.66/0.98      ( r4_lattice3(sK4,sK2(X0_52,sK4,X0_55),X0_55)
% 3.66/0.98      | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_997]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7108,plain,
% 3.66/0.98      ( r4_lattice3(sK4,X0_52,X0_55)
% 3.66/0.98      | ~ r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55)) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_4580,c_2372]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1341,plain,
% 3.66/0.98      ( r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1342,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1341]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1346,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.66/0.98      | r3_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1342,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1347,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1346]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2362,plain,
% 3.66/0.98      ( r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | r2_hidden(sK0(sK4,X0_52,X0_53),X0_53)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1347]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7539,plain,
% 3.66/0.98      ( r4_lattice3(sK4,sK0(sK4,X0_52,a_2_2_lattice3(sK4,X0_55)),X0_55)
% 3.66/0.98      | r3_lattice3(sK4,X0_52,a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_7108,c_2362]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7683,plain,
% 3.66/0.98      ( r3_lattice3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_4882,c_7539]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7685,plain,
% 3.66/0.98      ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_7683]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_9,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r1_lattices(X0,X1,X3)
% 3.66/0.98      | ~ r2_hidden(X3,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1293,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r1_lattices(X0,X1,X3)
% 3.66/0.98      | ~ r2_hidden(X3,X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1294,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r1_lattices(sK4,X0,X2)
% 3.66/0.98      | ~ r2_hidden(X2,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1293]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1298,plain,
% 3.66/0.98      ( ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ r2_hidden(X2,X1)
% 3.66/0.98      | r1_lattices(sK4,X0,X2)
% 3.66/0.98      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1294,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1299,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r1_lattices(sK4,X0,X2)
% 3.66/0.98      | ~ r2_hidden(X2,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1298]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2364,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | r1_lattices(sK4,X0_52,X1_52)
% 3.66/0.98      | ~ r2_hidden(X1_52,X0_53)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(X1_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1299]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3156,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0_52,a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | r1_lattices(sK4,X0_52,k15_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ r2_hidden(k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2364]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4349,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),a_2_2_lattice3(sK4,X1_55))
% 3.66/0.98      | r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),k15_lattice3(sK4,X1_55))
% 3.66/0.98      | ~ r2_hidden(k15_lattice3(sK4,X1_55),a_2_2_lattice3(sK4,X1_55))
% 3.66/0.98      | ~ m1_subset_1(sK3(sK4,k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X1_55)),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X1_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3156]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4353,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | r1_lattices(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),k15_lattice3(sK4,sK5))
% 3.66/0.98      | ~ r2_hidden(k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ m1_subset_1(sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_4349]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_21,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1 ),
% 3.66/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_943,plain,
% 3.66/0.98      ( ~ r3_lattice3(X0,X1,X2)
% 3.66/0.98      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | k16_lattice3(X0,X2) = X1
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_944,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_943]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_948,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.66/0.98      | ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_944,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_949,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0,X1)
% 3.66/0.98      | r3_lattice3(sK4,sK3(sK4,X0,X1),X1)
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X1) = X0 ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_948]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2373,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | r3_lattice3(sK4,sK3(sK4,X0_52,X0_53),X0_53)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = X0_52 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_949]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3133,plain,
% 3.66/0.98      ( r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),X0_53)
% 3.66/0.98      | ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2373]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3695,plain,
% 3.66/0.98      ( r3_lattice3(sK4,sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3133]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2374,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,X0_52,X0_53)
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 3.66/0.98      | m1_subset_1(sK3(sK4,X0_52,X0_53),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = X0_52 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_925]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3134,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_53)
% 3.66/0.98      | m1_subset_1(sK3(sK4,k15_lattice3(sK4,X0_55),X0_53),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,X0_53) = k15_lattice3(sK4,X0_55) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2374]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3641,plain,
% 3.66/0.98      ( ~ r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | m1_subset_1(sK3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5)),u1_struct_0(sK4))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4))
% 3.66/0.98      | k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) = k15_lattice3(sK4,sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3134]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3126,plain,
% 3.66/0.98      ( k15_lattice3(sK4,sK5) = k15_lattice3(sK4,sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2379]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3089,plain,
% 3.66/0.98      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) != X0_52
% 3.66/0.98      | k15_lattice3(sK4,sK5) != X0_52
% 3.66/0.98      | k15_lattice3(sK4,sK5) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2380]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3125,plain,
% 3.66/0.98      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) != k15_lattice3(sK4,sK5)
% 3.66/0.98      | k15_lattice3(sK4,sK5) = k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | k15_lattice3(sK4,sK5) != k15_lattice3(sK4,sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3089]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_16,plain,
% 3.66/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.66/0.98      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1009,plain,
% 3.66/0.98      ( ~ r4_lattice3(X0,X1,X2)
% 3.66/0.98      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.66/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1010,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.66/0.98      | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_1009]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1014,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.66/0.98      | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1010,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1015,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0,X1)
% 3.66/0.98      | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.66/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1014]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2371,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,X0_52,X0_55)
% 3.66/0.98      | r2_hidden(X0_52,a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(X0_52,u1_struct_0(sK4)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_1015]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3019,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55)
% 3.66/0.98      | r2_hidden(k15_lattice3(sK4,X0_55),a_2_2_lattice3(sK4,X0_55))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2371]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3021,plain,
% 3.66/0.98      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK5),sK5)
% 3.66/0.98      | r2_hidden(k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK5))
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3019]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2429,plain,
% 3.66/0.98      ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2365]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_14,plain,
% 3.66/0.98      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.66/0.98      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_180,plain,
% 3.66/0.98      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.66/0.98      | ~ v4_lattice3(X0)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_14,c_15]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_862,plain,
% 3.66/0.98      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 3.66/0.98      | ~ l3_lattices(X0)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ v10_lattices(X0)
% 3.66/0.98      | sK4 != X0 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_180,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_863,plain,
% 3.66/0.98      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0)
% 3.66/0.98      | ~ l3_lattices(sK4)
% 3.66/0.98      | v2_struct_0(sK4)
% 3.66/0.98      | ~ v10_lattices(sK4) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_862]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_867,plain,
% 3.66/0.98      ( r4_lattice3(sK4,k15_lattice3(sK4,X0),X0) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_863,c_29,c_28,c_26]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2376,plain,
% 3.66/0.98      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X0_55) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_867]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2396,plain,
% 3.66/0.98      ( r4_lattice3(sK4,k15_lattice3(sK4,sK5),sK5) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2376]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_25,negated_conjecture,
% 3.66/0.98      ( k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
% 3.66/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2377,negated_conjecture,
% 3.66/0.98      ( k15_lattice3(sK4,sK5) != k16_lattice3(sK4,a_2_2_lattice3(sK4,sK5)) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(contradiction,plain,
% 3.66/0.98      ( $false ),
% 3.66/0.98      inference(minisat,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_11668,c_7685,c_4353,c_3695,c_3641,c_3126,c_3125,
% 3.66/0.98                 c_3021,c_2429,c_2396,c_2377]) ).
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  ------                               Statistics
% 3.66/0.98  
% 3.66/0.98  ------ Selected
% 3.66/0.98  
% 3.66/0.98  total_time:                             0.38
% 3.66/0.98  
%------------------------------------------------------------------------------
