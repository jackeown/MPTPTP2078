%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:17 EST 2020

% Result     : Theorem 23.61s
% Output     : CNFRefutation 23.61s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 657 expanded)
%              Number of clauses        :   93 ( 173 expanded)
%              Number of leaves         :   17 ( 193 expanded)
%              Depth                    :   28
%              Number of atoms          :  969 (5080 expanded)
%              Number of equality atoms :  251 ( 304 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

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
    inference(flattening,[],[f11])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r2_hidden(sK8(X3),X2)
        & r3_lattices(X0,X3,sK8(X3))
        & m1_subset_1(sK8(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
     => ( ~ r3_lattices(X0,k15_lattice3(X0,sK6),k15_lattice3(X0,sK7))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,sK7)
                & r3_lattices(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,sK6)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
          ( ~ r3_lattices(sK5,k15_lattice3(sK5,X1),k15_lattice3(sK5,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK5,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK5)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) )
      & l3_lattices(sK5)
      & v4_lattice3(sK5)
      & v10_lattices(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7))
    & ! [X3] :
        ( ( r2_hidden(sK8(X3),sK7)
          & r3_lattices(sK5,X3,sK8(X3))
          & m1_subset_1(sK8(X3),u1_struct_0(sK5)) )
        | ~ r2_hidden(X3,sK6)
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    & l3_lattices(sK5)
    & v4_lattice3(sK5)
    & v10_lattices(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f49,f48,f47])).

fof(f82,plain,(
    ! [X3] :
      ( r2_hidden(sK8(X3),sK7)
      | ~ r2_hidden(X3,sK6)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X3] :
      ( r3_lattices(sK5,X3,sK8(X3))
      | ~ r2_hidden(X3,sK6)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X2),X2)
        & r3_lattices(X1,X5,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
            & r3_lattices(X1,sK3(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X2)
            & r3_lattices(X1,sK3(X0,X1,X2),sK4(X0,X1,X2))
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f77,plain,(
    v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X3] :
      ( m1_subset_1(sK8(X3),u1_struct_0(sK5))
      | ~ r2_hidden(X3,sK6)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f74,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK1(X0,X1,X2))
        & r4_lattice3(X0,sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_341,plain,
    ( m1_subset_1(k15_lattice3(X0_52,X0_54),u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_916,plain,
    ( m1_subset_1(k15_lattice3(X0_52,X0_54),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_1,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_347,plain,
    ( r4_lattice3(X0_52,X0_53,X0_54)
    | r2_hidden(sK0(X0_52,X0_53,X0_54),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_910,plain,
    ( r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
    | r2_hidden(sK0(X0_52,X0_53,X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_2,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_346,plain,
    ( r4_lattice3(X0_52,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(sK0(X0_52,X0_53,X0_54),u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_911,plain,
    ( r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK0(X0_52,X0_53,X0_54),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK8(X0),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_324,negated_conjecture,
    ( ~ r2_hidden(X0_53,sK6)
    | r2_hidden(sK8(X0_53),sK7)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_933,plain,
    ( r2_hidden(X0_53,sK6) != iProver_top
    | r2_hidden(sK8(X0_53),sK7) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_2690,plain,
    ( r4_lattice3(sK5,X0_53,X0_54) = iProver_top
    | r2_hidden(sK0(sK5,X0_53,X0_54),sK6) != iProver_top
    | r2_hidden(sK8(sK0(sK5,X0_53,X0_54)),sK7) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_933])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( l3_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2900,plain,
    ( r4_lattice3(sK5,X0_53,X0_54) = iProver_top
    | r2_hidden(sK0(sK5,X0_53,X0_54),sK6) != iProver_top
    | r2_hidden(sK8(sK0(sK5,X0_53,X0_54)),sK7) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_33,c_36])).

cnf(c_27,negated_conjecture,
    ( r3_lattices(sK5,X0,sK8(X0))
    | ~ r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_323,negated_conjecture,
    ( r3_lattices(sK5,X0_53,sK8(X0_53))
    | ~ r2_hidden(X0_53,sK6)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_934,plain,
    ( r3_lattices(sK5,X0_53,sK8(X0_53)) = iProver_top
    | r2_hidden(X0_53,sK6) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_14,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_5_lattice3(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_336,plain,
    ( ~ r3_lattices(X0_52,X0_53,X1_53)
    | ~ r2_hidden(X1_53,X0_54)
    | r2_hidden(X0_53,a_2_5_lattice3(X0_52,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_921,plain,
    ( r3_lattices(X0_52,X0_53,X1_53) != iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top
    | r2_hidden(X0_53,a_2_5_lattice3(X0_52,X0_54)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_7620,plain,
    ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
    | r2_hidden(X0_53,sK6) != iProver_top
    | r2_hidden(sK8(X0_53),X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK8(X0_53),u1_struct_0(sK5)) != iProver_top
    | v10_lattices(sK5) != iProver_top
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_921])).

cnf(c_5177,plain,
    ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54))
    | ~ r2_hidden(X0_53,sK6)
    | ~ r2_hidden(sK8(X0_53),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8(X0_53),u1_struct_0(sK5))
    | ~ v10_lattices(sK5)
    | ~ v4_lattice3(sK5)
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(resolution,[status(thm)],[c_336,c_323])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( v4_lattice3(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(sK8(X0),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_322,negated_conjecture,
    ( ~ r2_hidden(X0_53,sK6)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | m1_subset_1(sK8(X0_53),u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5569,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
    | ~ r2_hidden(sK8(X0_53),X0_54)
    | ~ r2_hidden(X0_53,sK6)
    | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5177,c_32,c_31,c_30,c_29,c_322])).

cnf(c_5570,plain,
    ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54))
    | ~ r2_hidden(X0_53,sK6)
    | ~ r2_hidden(sK8(X0_53),X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_5569])).

cnf(c_5571,plain,
    ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
    | r2_hidden(X0_53,sK6) != iProver_top
    | r2_hidden(sK8(X0_53),X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5570])).

cnf(c_8976,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8(X0_53),X0_54) != iProver_top
    | r2_hidden(X0_53,sK6) != iProver_top
    | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7620,c_5571])).

cnf(c_8977,plain,
    ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
    | r2_hidden(X0_53,sK6) != iProver_top
    | r2_hidden(sK8(X0_53),X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8976])).

cnf(c_319,negated_conjecture,
    ( v10_lattices(sK5) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_938,plain,
    ( v10_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_24,plain,
    ( ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_326,plain,
    ( ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k15_lattice3(X0_52,a_2_5_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_931,plain,
    ( k15_lattice3(X0_52,a_2_5_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54)
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1838,plain,
    ( k15_lattice3(sK5,a_2_5_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54)
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_931])).

cnf(c_35,plain,
    ( v4_lattice3(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2316,plain,
    ( k15_lattice3(sK5,a_2_5_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1838,c_33,c_35,c_36])).

cnf(c_8,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_254,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_9])).

cnf(c_317,plain,
    ( r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X0_54)
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_254])).

cnf(c_940,plain,
    ( r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X0_54) = iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_2498,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),a_2_5_lattice3(sK5,X0_54)) = iProver_top
    | v10_lattices(sK5) != iProver_top
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_940])).

cnf(c_34,plain,
    ( v10_lattices(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2503,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),a_2_5_lattice3(sK5,X0_54)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_33,c_34,c_35,c_36])).

cnf(c_3,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r4_lattice3(X0,X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_345,plain,
    ( r1_lattices(X0_52,X0_53,X1_53)
    | ~ r4_lattice3(X0_52,X1_53,X0_54)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_912,plain,
    ( r1_lattices(X0_52,X0_53,X1_53) = iProver_top
    | r4_lattice3(X0_52,X1_53,X0_54) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_3630,plain,
    ( r1_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_54)) = iProver_top
    | r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X1_54) != iProver_top
    | r2_hidden(X0_53,X1_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_912])).

cnf(c_7708,plain,
    ( r1_lattices(sK5,X0_53,k15_lattice3(sK5,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_3630])).

cnf(c_43649,plain,
    ( r1_lattices(sK5,X0_53,k15_lattice3(sK5,X0_54)) = iProver_top
    | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7708,c_33,c_36])).

cnf(c_0,plain,
    ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_348,plain,
    ( ~ r1_lattices(X0_52,sK0(X0_52,X0_53,X0_54),X0_53)
    | r4_lattice3(X0_52,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_909,plain,
    ( r1_lattices(X0_52,sK0(X0_52,X0_53,X0_54),X0_53) != iProver_top
    | r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_43659,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_43649,c_909])).

cnf(c_1361,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l3_lattices(sK5) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1365,plain,
    ( m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_47439,plain,
    ( m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
    | r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43659,c_33,c_36,c_1365])).

cnf(c_47440,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47439])).

cnf(c_47449,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
    | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
    | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_47440])).

cnf(c_68727,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
    | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_911,c_47449])).

cnf(c_69162,plain,
    ( r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
    | r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68727,c_33,c_36,c_1365])).

cnf(c_69163,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
    | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_69162])).

cnf(c_69172,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),X0_54) = iProver_top
    | r2_hidden(sK0(sK5,k15_lattice3(sK5,sK7),X0_54),sK6) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2900,c_69163])).

cnf(c_71673,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) = iProver_top
    | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_69172])).

cnf(c_10,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_340,plain,
    ( ~ r4_lattice3(X0_52,X0_53,X0_54)
    | r2_hidden(X0_53,a_2_2_lattice3(X0_52,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_917,plain,
    ( r4_lattice3(X0_52,X0_53,X0_54) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(X0_52,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_20,plain,
    ( ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_330,plain,
    ( ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52)
    | k16_lattice3(X0_52,a_2_2_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_927,plain,
    ( k16_lattice3(X0_52,a_2_2_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54)
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_1781,plain,
    ( k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54)
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_927])).

cnf(c_2054,plain,
    ( k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1781,c_33,c_35,c_36])).

cnf(c_21,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_329,plain,
    ( r3_lattices(X0_52,k16_lattice3(X0_52,X0_54),X0_53)
    | ~ r2_hidden(X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ v10_lattices(X0_52)
    | ~ v4_lattice3(X0_52)
    | v2_struct_0(X0_52)
    | ~ l3_lattices(X0_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_928,plain,
    ( r3_lattices(X0_52,k16_lattice3(X0_52,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v10_lattices(X0_52) != iProver_top
    | v4_lattice3(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l3_lattices(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_5432,plain,
    ( r3_lattices(sK5,k15_lattice3(sK5,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v10_lattices(sK5) != iProver_top
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_928])).

cnf(c_10504,plain,
    ( r3_lattices(sK5,k15_lattice3(sK5,X0_54),X0_53) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK5,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5432,c_33,c_34,c_35,c_36])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_325,negated_conjecture,
    ( ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_932,plain,
    ( r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_10514,plain,
    ( r2_hidden(k15_lattice3(sK5,sK7),a_2_2_lattice3(sK5,sK6)) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10504,c_932])).

cnf(c_10554,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top
    | v10_lattices(sK5) != iProver_top
    | v4_lattice3(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_10514])).

cnf(c_10894,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
    | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10554,c_33,c_34,c_35,c_36])).

cnf(c_10900,plain,
    ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_10894])).

cnf(c_73944,plain,
    ( m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71673,c_33,c_36,c_10900])).

cnf(c_73949,plain,
    ( v2_struct_0(sK5) = iProver_top
    | l3_lattices(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_73944])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73949,c_36,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:55:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.61/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.61/3.49  
% 23.61/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.61/3.49  
% 23.61/3.49  ------  iProver source info
% 23.61/3.49  
% 23.61/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.61/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.61/3.49  git: non_committed_changes: false
% 23.61/3.49  git: last_make_outside_of_git: false
% 23.61/3.49  
% 23.61/3.49  ------ 
% 23.61/3.49  ------ Parsing...
% 23.61/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.61/3.49  
% 23.61/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.61/3.49  
% 23.61/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.61/3.49  
% 23.61/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.61/3.49  ------ Proving...
% 23.61/3.49  ------ Problem Properties 
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  clauses                                 33
% 23.61/3.49  conjectures                             8
% 23.61/3.49  EPR                                     4
% 23.61/3.49  Horn                                    8
% 23.61/3.49  unary                                   5
% 23.61/3.49  binary                                  0
% 23.61/3.49  lits                                    168
% 23.61/3.49  lits eq                                 8
% 23.61/3.49  fd_pure                                 0
% 23.61/3.49  fd_pseudo                               0
% 23.61/3.49  fd_cond                                 0
% 23.61/3.49  fd_pseudo_cond                          3
% 23.61/3.49  AC symbols                              0
% 23.61/3.49  
% 23.61/3.49  ------ Input Options Time Limit: Unbounded
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  ------ 
% 23.61/3.49  Current options:
% 23.61/3.49  ------ 
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  ------ Proving...
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  % SZS status Theorem for theBenchmark.p
% 23.61/3.49  
% 23.61/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.61/3.49  
% 23.61/3.49  fof(f3,axiom,(
% 23.61/3.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f15,plain,(
% 23.61/3.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f3])).
% 23.61/3.49  
% 23.61/3.49  fof(f16,plain,(
% 23.61/3.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f15])).
% 23.61/3.49  
% 23.61/3.49  fof(f60,plain,(
% 23.61/3.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f16])).
% 23.61/3.49  
% 23.61/3.49  fof(f1,axiom,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f11,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f1])).
% 23.61/3.49  
% 23.61/3.49  fof(f12,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f11])).
% 23.61/3.49  
% 23.61/3.49  fof(f29,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(nnf_transformation,[],[f12])).
% 23.61/3.49  
% 23.61/3.49  fof(f30,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(rectify,[],[f29])).
% 23.61/3.49  
% 23.61/3.49  fof(f31,plain,(
% 23.61/3.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f32,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 23.61/3.49  
% 23.61/3.49  fof(f53,plain,(
% 23.61/3.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f32])).
% 23.61/3.49  
% 23.61/3.49  fof(f52,plain,(
% 23.61/3.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f32])).
% 23.61/3.49  
% 23.61/3.49  fof(f9,conjecture,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f10,negated_conjecture,(
% 23.61/3.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 23.61/3.49    inference(negated_conjecture,[],[f9])).
% 23.61/3.49  
% 23.61/3.49  fof(f27,plain,(
% 23.61/3.49    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f10])).
% 23.61/3.49  
% 23.61/3.49  fof(f28,plain,(
% 23.61/3.49    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f27])).
% 23.61/3.49  
% 23.61/3.49  fof(f49,plain,(
% 23.61/3.49    ( ! [X2,X0] : (! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r2_hidden(sK8(X3),X2) & r3_lattices(X0,X3,sK8(X3)) & m1_subset_1(sK8(X3),u1_struct_0(X0))))) )),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f48,plain,(
% 23.61/3.49    ( ! [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) => (~r3_lattices(X0,k15_lattice3(X0,sK6),k15_lattice3(X0,sK7)) & ! [X3] : (? [X4] : (r2_hidden(X4,sK7) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,u1_struct_0(X0))))) )),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f47,plain,(
% 23.61/3.49    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK5,k15_lattice3(sK5,X1),k15_lattice3(sK5,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK5,X3,X4) & m1_subset_1(X4,u1_struct_0(sK5))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK5)))) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5))),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f50,plain,(
% 23.61/3.49    (~r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) & ! [X3] : ((r2_hidden(sK8(X3),sK7) & r3_lattices(sK5,X3,sK8(X3)) & m1_subset_1(sK8(X3),u1_struct_0(sK5))) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,u1_struct_0(sK5)))) & l3_lattices(sK5) & v4_lattice3(sK5) & v10_lattices(sK5) & ~v2_struct_0(sK5)),
% 23.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f49,f48,f47])).
% 23.61/3.49  
% 23.61/3.49  fof(f82,plain,(
% 23.61/3.49    ( ! [X3] : (r2_hidden(sK8(X3),sK7) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,u1_struct_0(sK5))) )),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f76,plain,(
% 23.61/3.49    ~v2_struct_0(sK5)),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f79,plain,(
% 23.61/3.49    l3_lattices(sK5)),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f81,plain,(
% 23.61/3.49    ( ! [X3] : (r3_lattices(sK5,X3,sK8(X3)) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,u1_struct_0(sK5))) )),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f5,axiom,(
% 23.61/3.49    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f19,plain,(
% 23.61/3.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 23.61/3.49    inference(ennf_transformation,[],[f5])).
% 23.61/3.49  
% 23.61/3.49  fof(f20,plain,(
% 23.61/3.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(flattening,[],[f19])).
% 23.61/3.49  
% 23.61/3.49  fof(f42,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(nnf_transformation,[],[f20])).
% 23.61/3.49  
% 23.61/3.49  fof(f43,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(rectify,[],[f42])).
% 23.61/3.49  
% 23.61/3.49  fof(f45,plain,(
% 23.61/3.49    ( ! [X5] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK4(X0,X1,X2),X2) & r3_lattices(X1,X5,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))) )),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f44,plain,(
% 23.61/3.49    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK3(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f46,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK4(X0,X1,X2),X2) & r3_lattices(X1,sK3(X0,X1,X2),sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).
% 23.61/3.49  
% 23.61/3.49  fof(f70,plain,(
% 23.61/3.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f46])).
% 23.61/3.49  
% 23.61/3.49  fof(f87,plain,(
% 23.61/3.49    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.61/3.49    inference(equality_resolution,[],[f70])).
% 23.61/3.49  
% 23.61/3.49  fof(f77,plain,(
% 23.61/3.49    v10_lattices(sK5)),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f78,plain,(
% 23.61/3.49    v4_lattice3(sK5)),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f80,plain,(
% 23.61/3.49    ( ! [X3] : (m1_subset_1(sK8(X3),u1_struct_0(sK5)) | ~r2_hidden(X3,sK6) | ~m1_subset_1(X3,u1_struct_0(sK5))) )),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  fof(f8,axiom,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f25,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f8])).
% 23.61/3.49  
% 23.61/3.49  fof(f26,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f25])).
% 23.61/3.49  
% 23.61/3.49  fof(f74,plain,(
% 23.61/3.49    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f26])).
% 23.61/3.49  
% 23.61/3.49  fof(f2,axiom,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f13,plain,(
% 23.61/3.49    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f2])).
% 23.61/3.49  
% 23.61/3.49  fof(f14,plain,(
% 23.61/3.49    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f13])).
% 23.61/3.49  
% 23.61/3.49  fof(f33,plain,(
% 23.61/3.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(nnf_transformation,[],[f14])).
% 23.61/3.49  
% 23.61/3.49  fof(f34,plain,(
% 23.61/3.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f33])).
% 23.61/3.49  
% 23.61/3.49  fof(f35,plain,(
% 23.61/3.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(rectify,[],[f34])).
% 23.61/3.49  
% 23.61/3.49  fof(f36,plain,(
% 23.61/3.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f37,plain,(
% 23.61/3.49    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK1(X0,X1,X2)) & r4_lattice3(X0,sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 23.61/3.49  
% 23.61/3.49  fof(f55,plain,(
% 23.61/3.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f37])).
% 23.61/3.49  
% 23.61/3.49  fof(f85,plain,(
% 23.61/3.49    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(equality_resolution,[],[f55])).
% 23.61/3.49  
% 23.61/3.49  fof(f51,plain,(
% 23.61/3.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f32])).
% 23.61/3.49  
% 23.61/3.49  fof(f54,plain,(
% 23.61/3.49    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK0(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f32])).
% 23.61/3.49  
% 23.61/3.49  fof(f4,axiom,(
% 23.61/3.49    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f17,plain,(
% 23.61/3.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 23.61/3.49    inference(ennf_transformation,[],[f4])).
% 23.61/3.49  
% 23.61/3.49  fof(f18,plain,(
% 23.61/3.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(flattening,[],[f17])).
% 23.61/3.49  
% 23.61/3.49  fof(f38,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(nnf_transformation,[],[f18])).
% 23.61/3.49  
% 23.61/3.49  fof(f39,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(rectify,[],[f38])).
% 23.61/3.49  
% 23.61/3.49  fof(f40,plain,(
% 23.61/3.49    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 23.61/3.49    introduced(choice_axiom,[])).
% 23.61/3.49  
% 23.61/3.49  fof(f41,plain,(
% 23.61/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 23.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 23.61/3.49  
% 23.61/3.49  fof(f64,plain,(
% 23.61/3.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f41])).
% 23.61/3.49  
% 23.61/3.49  fof(f86,plain,(
% 23.61/3.49    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 23.61/3.49    inference(equality_resolution,[],[f64])).
% 23.61/3.49  
% 23.61/3.49  fof(f6,axiom,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f21,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f6])).
% 23.61/3.49  
% 23.61/3.49  fof(f22,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f21])).
% 23.61/3.49  
% 23.61/3.49  fof(f71,plain,(
% 23.61/3.49    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f22])).
% 23.61/3.49  
% 23.61/3.49  fof(f7,axiom,(
% 23.61/3.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 23.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.61/3.49  
% 23.61/3.49  fof(f23,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 23.61/3.49    inference(ennf_transformation,[],[f7])).
% 23.61/3.49  
% 23.61/3.49  fof(f24,plain,(
% 23.61/3.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 23.61/3.49    inference(flattening,[],[f23])).
% 23.61/3.49  
% 23.61/3.49  fof(f73,plain,(
% 23.61/3.49    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 23.61/3.49    inference(cnf_transformation,[],[f24])).
% 23.61/3.49  
% 23.61/3.49  fof(f83,plain,(
% 23.61/3.49    ~r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7))),
% 23.61/3.49    inference(cnf_transformation,[],[f50])).
% 23.61/3.49  
% 23.61/3.49  cnf(c_9,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_341,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(X0_52,X0_54),u1_struct_0(X0_52))
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_9]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_916,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(X0_52,X0_54),u1_struct_0(X0_52)) = iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_1,plain,
% 23.61/3.49      ( r4_lattice3(X0,X1,X2)
% 23.61/3.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_347,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,X0_53,X0_54)
% 23.61/3.49      | r2_hidden(sK0(X0_52,X0_53,X0_54),X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_1]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_910,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(X0_52,X0_53,X0_54),X0_54) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2,plain,
% 23.61/3.49      ( r4_lattice3(X0,X1,X2)
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_346,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,X0_53,X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | m1_subset_1(sK0(X0_52,X0_53,X0_54),u1_struct_0(X0_52))
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_2]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_911,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | m1_subset_1(sK0(X0_52,X0_53,X0_54),u1_struct_0(X0_52)) = iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_26,negated_conjecture,
% 23.61/3.49      ( ~ r2_hidden(X0,sK6)
% 23.61/3.49      | r2_hidden(sK8(X0),sK7)
% 23.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 23.61/3.49      inference(cnf_transformation,[],[f82]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_324,negated_conjecture,
% 23.61/3.49      ( ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | r2_hidden(sK8(X0_53),sK7)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_26]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_933,plain,
% 23.61/3.49      ( r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(X0_53),sK7) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2690,plain,
% 23.61/3.49      ( r4_lattice3(sK5,X0_53,X0_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,X0_53,X0_54),sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(sK0(sK5,X0_53,X0_54)),sK7) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_911,c_933]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_32,negated_conjecture,
% 23.61/3.49      ( ~ v2_struct_0(sK5) ),
% 23.61/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_33,plain,
% 23.61/3.49      ( v2_struct_0(sK5) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_29,negated_conjecture,
% 23.61/3.49      ( l3_lattices(sK5) ),
% 23.61/3.49      inference(cnf_transformation,[],[f79]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_36,plain,
% 23.61/3.49      ( l3_lattices(sK5) = iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2900,plain,
% 23.61/3.49      ( r4_lattice3(sK5,X0_53,X0_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,X0_53,X0_54),sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(sK0(sK5,X0_53,X0_54)),sK7) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_2690,c_33,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_27,negated_conjecture,
% 23.61/3.49      ( r3_lattices(sK5,X0,sK8(X0))
% 23.61/3.49      | ~ r2_hidden(X0,sK6)
% 23.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 23.61/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_323,negated_conjecture,
% 23.61/3.49      ( r3_lattices(sK5,X0_53,sK8(X0_53))
% 23.61/3.49      | ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_27]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_934,plain,
% 23.61/3.49      ( r3_lattices(sK5,X0_53,sK8(X0_53)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_14,plain,
% 23.61/3.49      ( ~ r3_lattices(X0,X1,X2)
% 23.61/3.49      | ~ r2_hidden(X2,X3)
% 23.61/3.49      | r2_hidden(X1,a_2_5_lattice3(X0,X3))
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.61/3.49      | ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f87]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_336,plain,
% 23.61/3.49      ( ~ r3_lattices(X0_52,X0_53,X1_53)
% 23.61/3.49      | ~ r2_hidden(X1_53,X0_54)
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(X0_52,X0_54))
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 23.61/3.49      | ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_14]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_921,plain,
% 23.61/3.49      ( r3_lattices(X0_52,X0_53,X1_53) != iProver_top
% 23.61/3.49      | r2_hidden(X1_53,X0_54) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(X0_52,X0_54)) = iProver_top
% 23.61/3.49      | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_7620,plain,
% 23.61/3.49      ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(X0_53),X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | m1_subset_1(sK8(X0_53),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v10_lattices(sK5) != iProver_top
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_934,c_921]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_5177,plain,
% 23.61/3.49      ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54))
% 23.61/3.49      | ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | ~ r2_hidden(sK8(X0_53),X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 23.61/3.49      | ~ m1_subset_1(sK8(X0_53),u1_struct_0(sK5))
% 23.61/3.49      | ~ v10_lattices(sK5)
% 23.61/3.49      | ~ v4_lattice3(sK5)
% 23.61/3.49      | v2_struct_0(sK5)
% 23.61/3.49      | ~ l3_lattices(sK5) ),
% 23.61/3.49      inference(resolution,[status(thm)],[c_336,c_323]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_31,negated_conjecture,
% 23.61/3.49      ( v10_lattices(sK5) ),
% 23.61/3.49      inference(cnf_transformation,[],[f77]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_30,negated_conjecture,
% 23.61/3.49      ( v4_lattice3(sK5) ),
% 23.61/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_28,negated_conjecture,
% 23.61/3.49      ( ~ r2_hidden(X0,sK6)
% 23.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 23.61/3.49      | m1_subset_1(sK8(X0),u1_struct_0(sK5)) ),
% 23.61/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_322,negated_conjecture,
% 23.61/3.49      ( ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 23.61/3.49      | m1_subset_1(sK8(X0_53),u1_struct_0(sK5)) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_28]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_5569,plain,
% 23.61/3.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK5))
% 23.61/3.49      | ~ r2_hidden(sK8(X0_53),X0_54)
% 23.61/3.49      | ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_5177,c_32,c_31,c_30,c_29,c_322]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_5570,plain,
% 23.61/3.49      ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54))
% 23.61/3.49      | ~ r2_hidden(X0_53,sK6)
% 23.61/3.49      | ~ r2_hidden(sK8(X0_53),X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(sK5)) ),
% 23.61/3.49      inference(renaming,[status(thm)],[c_5569]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_5571,plain,
% 23.61/3.49      ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(X0_53),X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_5570]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_8976,plain,
% 23.61/3.49      ( m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(X0_53),X0_54) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_7620,c_5571]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_8977,plain,
% 23.61/3.49      ( r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(X0_53),X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(renaming,[status(thm)],[c_8976]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_319,negated_conjecture,
% 23.61/3.49      ( v10_lattices(sK5) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_31]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_938,plain,
% 23.61/3.49      ( v10_lattices(sK5) = iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_24,plain,
% 23.61/3.49      ( ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0)
% 23.61/3.49      | k15_lattice3(X0,a_2_5_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 23.61/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_326,plain,
% 23.61/3.49      ( ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52)
% 23.61/3.49      | k15_lattice3(X0_52,a_2_5_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_24]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_931,plain,
% 23.61/3.49      ( k15_lattice3(X0_52,a_2_5_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54)
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_1838,plain,
% 23.61/3.49      ( k15_lattice3(sK5,a_2_5_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54)
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_938,c_931]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_35,plain,
% 23.61/3.49      ( v4_lattice3(sK5) = iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2316,plain,
% 23.61/3.49      ( k15_lattice3(sK5,a_2_5_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54) ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_1838,c_33,c_35,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_8,plain,
% 23.61/3.49      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 23.61/3.49      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 23.61/3.49      | ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_254,plain,
% 23.61/3.49      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 23.61/3.49      | ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(global_propositional_subsumption,[status(thm)],[c_8,c_9]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_317,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X0_54)
% 23.61/3.49      | ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_254]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_940,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X0_54) = iProver_top
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2498,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),a_2_5_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | v10_lattices(sK5) != iProver_top
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_2316,c_940]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_34,plain,
% 23.61/3.49      ( v10_lattices(sK5) = iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2503,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),a_2_5_lattice3(sK5,X0_54)) = iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_2498,c_33,c_34,c_35,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_3,plain,
% 23.61/3.49      ( r1_lattices(X0,X1,X2)
% 23.61/3.49      | ~ r4_lattice3(X0,X2,X3)
% 23.61/3.49      | ~ r2_hidden(X1,X3)
% 23.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_345,plain,
% 23.61/3.49      ( r1_lattices(X0_52,X0_53,X1_53)
% 23.61/3.49      | ~ r4_lattice3(X0_52,X1_53,X0_54)
% 23.61/3.49      | ~ r2_hidden(X0_53,X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | ~ m1_subset_1(X1_53,u1_struct_0(X0_52))
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_3]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_912,plain,
% 23.61/3.49      ( r1_lattices(X0_52,X0_53,X1_53) = iProver_top
% 23.61/3.49      | r4_lattice3(X0_52,X1_53,X0_54) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X1_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_3630,plain,
% 23.61/3.49      ( r1_lattices(X0_52,X0_53,k15_lattice3(X0_52,X0_54)) = iProver_top
% 23.61/3.49      | r4_lattice3(X0_52,k15_lattice3(X0_52,X0_54),X1_54) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,X1_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_916,c_912]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_7708,plain,
% 23.61/3.49      ( r1_lattices(sK5,X0_53,k15_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_2503,c_3630]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_43649,plain,
% 23.61/3.49      ( r1_lattices(sK5,X0_53,k15_lattice3(sK5,X0_54)) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_5_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_7708,c_33,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_0,plain,
% 23.61/3.49      ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
% 23.61/3.49      | r4_lattice3(X0,X1,X2)
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_348,plain,
% 23.61/3.49      ( ~ r1_lattices(X0_52,sK0(X0_52,X0_53,X0_54),X0_53)
% 23.61/3.49      | r4_lattice3(X0_52,X0_53,X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_0]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_909,plain,
% 23.61/3.49      ( r1_lattices(X0_52,sK0(X0_52,X0_53,X0_54),X0_53) != iProver_top
% 23.61/3.49      | r4_lattice3(X0_52,X0_53,X0_54) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_43659,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_43649,c_909]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_1361,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5))
% 23.61/3.49      | v2_struct_0(sK5)
% 23.61/3.49      | ~ l3_lattices(sK5) ),
% 23.61/3.49      inference(instantiation,[status(thm)],[c_341]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_1365,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) = iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_47439,plain,
% 23.61/3.49      ( m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_43659,c_33,c_36,c_1365]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_47440,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),a_2_5_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(renaming,[status(thm)],[c_47439]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_47449,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_8977,c_47440]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_68727,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,X0_54),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_911,c_47449]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_69162,plain,
% 23.61/3.49      ( r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
% 23.61/3.49      | r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_68727,c_33,c_36,c_1365]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_69163,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,X0_54),X1_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54),sK6) != iProver_top
% 23.61/3.49      | r2_hidden(sK8(sK0(sK5,k15_lattice3(sK5,X0_54),X1_54)),X0_54) != iProver_top ),
% 23.61/3.49      inference(renaming,[status(thm)],[c_69162]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_69172,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),X0_54) = iProver_top
% 23.61/3.49      | r2_hidden(sK0(sK5,k15_lattice3(sK5,sK7),X0_54),sK6) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_2900,c_69163]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_71673,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) = iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_910,c_69172]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10,plain,
% 23.61/3.49      ( ~ r4_lattice3(X0,X1,X2)
% 23.61/3.49      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 23.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.61/3.49      | ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f86]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_340,plain,
% 23.61/3.49      ( ~ r4_lattice3(X0_52,X0_53,X0_54)
% 23.61/3.49      | r2_hidden(X0_53,a_2_2_lattice3(X0_52,X0_54))
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_10]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_917,plain,
% 23.61/3.49      ( r4_lattice3(X0_52,X0_53,X0_54) != iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_2_lattice3(X0_52,X0_54)) = iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_20,plain,
% 23.61/3.49      ( ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0)
% 23.61/3.49      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 23.61/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_330,plain,
% 23.61/3.49      ( ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52)
% 23.61/3.49      | k16_lattice3(X0_52,a_2_2_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_20]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_927,plain,
% 23.61/3.49      ( k16_lattice3(X0_52,a_2_2_lattice3(X0_52,X0_54)) = k15_lattice3(X0_52,X0_54)
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_1781,plain,
% 23.61/3.49      ( k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54)
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_938,c_927]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_2054,plain,
% 23.61/3.49      ( k16_lattice3(sK5,a_2_2_lattice3(sK5,X0_54)) = k15_lattice3(sK5,X0_54) ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_1781,c_33,c_35,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_21,plain,
% 23.61/3.49      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 23.61/3.49      | ~ r2_hidden(X2,X1)
% 23.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 23.61/3.49      | ~ v10_lattices(X0)
% 23.61/3.49      | ~ v4_lattice3(X0)
% 23.61/3.49      | v2_struct_0(X0)
% 23.61/3.49      | ~ l3_lattices(X0) ),
% 23.61/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_329,plain,
% 23.61/3.49      ( r3_lattices(X0_52,k16_lattice3(X0_52,X0_54),X0_53)
% 23.61/3.49      | ~ r2_hidden(X0_53,X0_54)
% 23.61/3.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 23.61/3.49      | ~ v10_lattices(X0_52)
% 23.61/3.49      | ~ v4_lattice3(X0_52)
% 23.61/3.49      | v2_struct_0(X0_52)
% 23.61/3.49      | ~ l3_lattices(X0_52) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_21]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_928,plain,
% 23.61/3.49      ( r3_lattices(X0_52,k16_lattice3(X0_52,X0_54),X0_53) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,X0_54) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 23.61/3.49      | v10_lattices(X0_52) != iProver_top
% 23.61/3.49      | v4_lattice3(X0_52) != iProver_top
% 23.61/3.49      | v2_struct_0(X0_52) = iProver_top
% 23.61/3.49      | l3_lattices(X0_52) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_5432,plain,
% 23.61/3.49      ( r3_lattices(sK5,k15_lattice3(sK5,X0_54),X0_53) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_2_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v10_lattices(sK5) != iProver_top
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_2054,c_928]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10504,plain,
% 23.61/3.49      ( r3_lattices(sK5,k15_lattice3(sK5,X0_54),X0_53) = iProver_top
% 23.61/3.49      | r2_hidden(X0_53,a_2_2_lattice3(sK5,X0_54)) != iProver_top
% 23.61/3.49      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_5432,c_33,c_34,c_35,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_25,negated_conjecture,
% 23.61/3.49      ( ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) ),
% 23.61/3.49      inference(cnf_transformation,[],[f83]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_325,negated_conjecture,
% 23.61/3.49      ( ~ r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) ),
% 23.61/3.49      inference(subtyping,[status(esa)],[c_25]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_932,plain,
% 23.61/3.49      ( r3_lattices(sK5,k15_lattice3(sK5,sK6),k15_lattice3(sK5,sK7)) != iProver_top ),
% 23.61/3.49      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10514,plain,
% 23.61/3.49      ( r2_hidden(k15_lattice3(sK5,sK7),a_2_2_lattice3(sK5,sK6)) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_10504,c_932]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10554,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top
% 23.61/3.49      | v10_lattices(sK5) != iProver_top
% 23.61/3.49      | v4_lattice3(sK5) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_917,c_10514]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10894,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
% 23.61/3.49      | m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_10554,c_33,c_34,c_35,c_36]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_10900,plain,
% 23.61/3.49      ( r4_lattice3(sK5,k15_lattice3(sK5,sK7),sK6) != iProver_top
% 23.61/3.49      | v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_916,c_10894]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_73944,plain,
% 23.61/3.49      ( m1_subset_1(k15_lattice3(sK5,sK7),u1_struct_0(sK5)) != iProver_top ),
% 23.61/3.49      inference(global_propositional_subsumption,
% 23.61/3.49                [status(thm)],
% 23.61/3.49                [c_71673,c_33,c_36,c_10900]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(c_73949,plain,
% 23.61/3.49      ( v2_struct_0(sK5) = iProver_top
% 23.61/3.49      | l3_lattices(sK5) != iProver_top ),
% 23.61/3.49      inference(superposition,[status(thm)],[c_916,c_73944]) ).
% 23.61/3.49  
% 23.61/3.49  cnf(contradiction,plain,
% 23.61/3.49      ( $false ),
% 23.61/3.49      inference(minisat,[status(thm)],[c_73949,c_36,c_33]) ).
% 23.61/3.49  
% 23.61/3.49  
% 23.61/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.61/3.49  
% 23.61/3.49  ------                               Statistics
% 23.61/3.49  
% 23.61/3.49  ------ Selected
% 23.61/3.49  
% 23.61/3.49  total_time:                             2.777
% 23.61/3.49  
%------------------------------------------------------------------------------
