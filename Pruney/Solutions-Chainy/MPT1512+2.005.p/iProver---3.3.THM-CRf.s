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
% DateTime   : Thu Dec  3 12:19:17 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  251 (3155 expanded)
%              Number of clauses        :  172 ( 852 expanded)
%              Number of leaves         :   16 ( 782 expanded)
%              Depth                    :   31
%              Number of atoms          : 1127 (18983 expanded)
%              Number of equality atoms :  210 ( 794 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5))
          | ~ r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6)) )
        & r1_tarski(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1))
            | ~ r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) )
    & r1_tarski(sK5,sK6)
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f50,f49])).

fof(f77,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f44])).

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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r3_lattices(X0,X4,X1)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f66])).

cnf(c_2,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_861,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_862,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_866,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_27])).

cnf(c_867,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_866])).

cnf(c_1617,plain,
    ( r3_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0_51,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_867])).

cnf(c_2091,plain,
    ( r3_lattice3(sK4,X0_51,X0_52) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_51,X0_52),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_6,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_771,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_772,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_776,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_27])).

cnf(c_777,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_1621,plain,
    ( r4_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0_51,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_777])).

cnf(c_2087,plain,
    ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,X0_51,X0_52),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1621])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK5 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_1636,plain,
    ( ~ r2_hidden(X0_51,sK5)
    | r2_hidden(X0_51,sK6) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_2073,plain,
    ( r2_hidden(X0_51,sK5) != iProver_top
    | r2_hidden(X0_51,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_2905,plain,
    ( r4_lattice3(sK4,X0_51,sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,X0_51,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2073])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | sK2(X0,sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_26,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_487,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | sK2(X0,sK4,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_27,c_26,c_24])).

cnf(c_1634,plain,
    ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52))
    | sK2(X0_51,sK4,X0_52) = X0_51 ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_2075,plain,
    ( sK2(X0_51,sK4,X0_52) = X0_51
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_3688,plain,
    ( sK2(sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)),sK4,X0_52) = sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52))
    | r3_lattice3(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_2075])).

cnf(c_20,plain,
    ( ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_536,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_537,plain,
    ( ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4)
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_27,c_26,c_24])).

cnf(c_1631,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)) = k15_lattice3(sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_18,plain,
    ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21])).

cnf(c_169,plain,
    ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_515,plain,
    ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_169,c_25])).

cnf(c_516,plain,
    ( r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_27,c_26,c_24])).

cnf(c_521,plain,
    ( r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_520])).

cnf(c_1632,plain,
    ( r3_lattices(sK4,X0_51,k16_lattice3(sK4,X0_52))
    | ~ r3_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_2077,plain,
    ( r3_lattices(sK4,X0_51,k16_lattice3(sK4,X0_52)) = iProver_top
    | r3_lattice3(sK4,X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_2913,plain,
    ( r3_lattices(sK4,X0_51,k15_lattice3(sK4,X0_52)) = iProver_top
    | r3_lattice3(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_2077])).

cnf(c_5237,plain,
    ( sK2(sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)),sK4,X0_52) = sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52))
    | r3_lattices(sK4,X0_51,k15_lattice3(sK4,X0_52)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3688,c_2913])).

cnf(c_22,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1637,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2072,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_2914,plain,
    ( r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
    | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_2072])).

cnf(c_5259,plain,
    ( sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6))
    | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_2914])).

cnf(c_9,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_708,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_709,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_713,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_27])).

cnf(c_1624,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_713])).

cnf(c_1690,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_1692,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_10,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_693,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_694,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_698,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_27])).

cnf(c_1625,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_698])).

cnf(c_3223,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_3224,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3223])).

cnf(c_3689,plain,
    ( r3_lattice3(sK4,X0_51,sK5) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_51,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_2073])).

cnf(c_19,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_161,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_10])).

cnf(c_500,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_25])).

cnf(c_501,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_505,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_27,c_26,c_24])).

cnf(c_1633,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_505])).

cnf(c_2076,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_2083,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_4,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_813,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattice3(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_814,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_818,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r3_lattice3(sK4,X0,X2)
    | r1_lattices(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_27])).

cnf(c_819,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattice3(sK4,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2) ),
    inference(renaming,[status(thm)],[c_818])).

cnf(c_1619,plain,
    ( r1_lattices(sK4,X0_51,X1_51)
    | ~ r3_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
    | ~ r2_hidden(X1_51,X0_52) ),
    inference(subtyping,[status(esa)],[c_819])).

cnf(c_2089,plain,
    ( r1_lattices(sK4,X0_51,X1_51) = iProver_top
    | r3_lattice3(sK4,X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_51,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_3294,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_52),X0_51) = iProver_top
    | r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_2089])).

cnf(c_4797,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_52),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2076,c_3294])).

cnf(c_1,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_882,plain,
    ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_883,plain,
    ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_882])).

cnf(c_887,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_883,c_27])).

cnf(c_888,plain,
    ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_887])).

cnf(c_1616,plain,
    ( ~ r1_lattices(sK4,X0_51,sK0(sK4,X0_51,X0_52))
    | r3_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_888])).

cnf(c_2092,plain,
    ( r1_lattices(sK4,X0_51,sK0(sK4,X0_51,X0_52)) != iProver_top
    | r3_lattice3(sK4,X0_51,X0_52) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_4979,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_4797,c_2092])).

cnf(c_1687,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_3,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_840,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_841,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_845,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_27])).

cnf(c_846,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_845])).

cnf(c_1618,plain,
    ( r3_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_51,X0_52),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_846])).

cnf(c_2151,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52)
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_2152,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2151])).

cnf(c_5022,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4979,c_1687,c_2152])).

cnf(c_5028,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3689,c_5022])).

cnf(c_5404,plain,
    ( sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5259,c_1692,c_3224,c_5028])).

cnf(c_7,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_750,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_751,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_27])).

cnf(c_756,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_755])).

cnf(c_1622,plain,
    ( r4_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_51,X0_52),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_756])).

cnf(c_2086,plain,
    ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,X0_51,X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_12,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_619,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_620,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_624,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_27,c_26,c_24])).

cnf(c_625,plain,
    ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_624])).

cnf(c_1627,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X0_52)
    | ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
    inference(subtyping,[status(esa)],[c_625])).

cnf(c_2081,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X0_52) = iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_14,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_464,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_465,plain,
    ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_469,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_27,c_26,c_24])).

cnf(c_470,plain,
    ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
    | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_1635,plain,
    ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4))
    | ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_2074,plain,
    ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_8,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_723,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_724,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_728,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattices(sK4,X2,X0)
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_27])).

cnf(c_729,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | r1_lattices(sK4,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_1623,plain,
    ( ~ r4_lattice3(sK4,X0_51,X0_52)
    | r1_lattices(sK4,X1_51,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
    | ~ r2_hidden(X1_51,X0_52) ),
    inference(subtyping,[status(esa)],[c_729])).

cnf(c_2085,plain,
    ( r4_lattice3(sK4,X0_51,X0_52) != iProver_top
    | r1_lattices(sK4,X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_51,X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_3122,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) != iProver_top
    | r1_lattices(sK4,X1_51,sK2(X0_51,sK4,X0_52)) = iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_51,X1_52) != iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2074,c_2085])).

cnf(c_5131,plain,
    ( r1_lattices(sK4,X0_51,sK2(X1_51,sK4,X0_52)) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,X0_52) != iProver_top
    | r2_hidden(X1_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_3122])).

cnf(c_5,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_792,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_793,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_27])).

cnf(c_798,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_1620,plain,
    ( r4_lattice3(sK4,X0_51,X0_52)
    | ~ r1_lattices(sK4,sK1(sK4,X0_51,X0_52),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_798])).

cnf(c_2088,plain,
    ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
    | r1_lattices(sK4,sK1(sK4,X0_51,X0_52),X0_51) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1620])).

cnf(c_5140,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
    | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_5131,c_2088])).

cnf(c_1659,plain,
    ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_5837,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
    | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5140,c_1659])).

cnf(c_5841,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
    | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_5837])).

cnf(c_5849,plain,
    ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
    | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5841,c_1659])).

cnf(c_5856,plain,
    ( r4_lattice3(sK4,sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6),X0_52) = iProver_top
    | r2_hidden(sK1(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52),sK6) != iProver_top
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5404,c_5849])).

cnf(c_5857,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52) = iProver_top
    | r2_hidden(sK1(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52),sK6) != iProver_top
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5856,c_5404])).

cnf(c_6687,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_5857])).

cnf(c_5409,plain,
    ( m1_subset_1(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5404,c_2074])).

cnf(c_6691,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
    | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6687,c_5409])).

cnf(c_6695,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_6691])).

cnf(c_9460,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top
    | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6695,c_1692])).

cnf(c_9461,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9460])).

cnf(c_11,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | ~ v4_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_637,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_638,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ v10_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_642,plain,
    ( r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_27,c_26,c_24])).

cnf(c_643,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_642])).

cnf(c_1626,plain,
    ( ~ r4_lattice3(sK4,X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
    inference(subtyping,[status(esa)],[c_643])).

cnf(c_2082,plain,
    ( r4_lattice3(sK4,X0_51,X0_52) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_5027,plain,
    ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2082,c_5022])).

cnf(c_5031,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5027,c_1631])).

cnf(c_2146,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52)
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_2147,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
    | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2146])).

cnf(c_5055,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
    | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5031,c_1690,c_2147])).

cnf(c_5056,plain,
    ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top
    | r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_5055])).

cnf(c_9474,plain,
    ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9461,c_5056])).

cnf(c_9577,plain,
    ( r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) = iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9474,c_2913])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9577,c_5028,c_3224,c_2914,c_1692])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:41:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.37/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.01  
% 3.37/1.01  ------  iProver source info
% 3.37/1.01  
% 3.37/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.01  git: non_committed_changes: false
% 3.37/1.01  git: last_make_outside_of_git: false
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options
% 3.37/1.01  
% 3.37/1.01  --out_options                           all
% 3.37/1.01  --tptp_safe_out                         true
% 3.37/1.01  --problem_path                          ""
% 3.37/1.01  --include_path                          ""
% 3.37/1.01  --clausifier                            res/vclausify_rel
% 3.37/1.01  --clausifier_options                    ""
% 3.37/1.01  --stdin                                 false
% 3.37/1.01  --stats_out                             all
% 3.37/1.01  
% 3.37/1.01  ------ General Options
% 3.37/1.01  
% 3.37/1.01  --fof                                   false
% 3.37/1.01  --time_out_real                         305.
% 3.37/1.01  --time_out_virtual                      -1.
% 3.37/1.01  --symbol_type_check                     false
% 3.37/1.01  --clausify_out                          false
% 3.37/1.01  --sig_cnt_out                           false
% 3.37/1.01  --trig_cnt_out                          false
% 3.37/1.01  --trig_cnt_out_tolerance                1.
% 3.37/1.01  --trig_cnt_out_sk_spl                   false
% 3.37/1.01  --abstr_cl_out                          false
% 3.37/1.01  
% 3.37/1.01  ------ Global Options
% 3.37/1.01  
% 3.37/1.01  --schedule                              default
% 3.37/1.01  --add_important_lit                     false
% 3.37/1.01  --prop_solver_per_cl                    1000
% 3.37/1.01  --min_unsat_core                        false
% 3.37/1.01  --soft_assumptions                      false
% 3.37/1.01  --soft_lemma_size                       3
% 3.37/1.01  --prop_impl_unit_size                   0
% 3.37/1.01  --prop_impl_unit                        []
% 3.37/1.01  --share_sel_clauses                     true
% 3.37/1.01  --reset_solvers                         false
% 3.37/1.01  --bc_imp_inh                            [conj_cone]
% 3.37/1.01  --conj_cone_tolerance                   3.
% 3.37/1.01  --extra_neg_conj                        none
% 3.37/1.01  --large_theory_mode                     true
% 3.37/1.01  --prolific_symb_bound                   200
% 3.37/1.01  --lt_threshold                          2000
% 3.37/1.01  --clause_weak_htbl                      true
% 3.37/1.01  --gc_record_bc_elim                     false
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing Options
% 3.37/1.01  
% 3.37/1.01  --preprocessing_flag                    true
% 3.37/1.01  --time_out_prep_mult                    0.1
% 3.37/1.01  --splitting_mode                        input
% 3.37/1.01  --splitting_grd                         true
% 3.37/1.01  --splitting_cvd                         false
% 3.37/1.01  --splitting_cvd_svl                     false
% 3.37/1.01  --splitting_nvd                         32
% 3.37/1.01  --sub_typing                            true
% 3.37/1.01  --prep_gs_sim                           true
% 3.37/1.01  --prep_unflatten                        true
% 3.37/1.01  --prep_res_sim                          true
% 3.37/1.01  --prep_upred                            true
% 3.37/1.01  --prep_sem_filter                       exhaustive
% 3.37/1.01  --prep_sem_filter_out                   false
% 3.37/1.01  --pred_elim                             true
% 3.37/1.01  --res_sim_input                         true
% 3.37/1.01  --eq_ax_congr_red                       true
% 3.37/1.01  --pure_diseq_elim                       true
% 3.37/1.01  --brand_transform                       false
% 3.37/1.01  --non_eq_to_eq                          false
% 3.37/1.01  --prep_def_merge                        true
% 3.37/1.01  --prep_def_merge_prop_impl              false
% 3.37/1.01  --prep_def_merge_mbd                    true
% 3.37/1.01  --prep_def_merge_tr_red                 false
% 3.37/1.01  --prep_def_merge_tr_cl                  false
% 3.37/1.01  --smt_preprocessing                     true
% 3.37/1.01  --smt_ac_axioms                         fast
% 3.37/1.01  --preprocessed_out                      false
% 3.37/1.01  --preprocessed_stats                    false
% 3.37/1.01  
% 3.37/1.01  ------ Abstraction refinement Options
% 3.37/1.01  
% 3.37/1.01  --abstr_ref                             []
% 3.37/1.01  --abstr_ref_prep                        false
% 3.37/1.01  --abstr_ref_until_sat                   false
% 3.37/1.01  --abstr_ref_sig_restrict                funpre
% 3.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.01  --abstr_ref_under                       []
% 3.37/1.01  
% 3.37/1.01  ------ SAT Options
% 3.37/1.01  
% 3.37/1.01  --sat_mode                              false
% 3.37/1.01  --sat_fm_restart_options                ""
% 3.37/1.01  --sat_gr_def                            false
% 3.37/1.01  --sat_epr_types                         true
% 3.37/1.01  --sat_non_cyclic_types                  false
% 3.37/1.01  --sat_finite_models                     false
% 3.37/1.01  --sat_fm_lemmas                         false
% 3.37/1.01  --sat_fm_prep                           false
% 3.37/1.01  --sat_fm_uc_incr                        true
% 3.37/1.01  --sat_out_model                         small
% 3.37/1.01  --sat_out_clauses                       false
% 3.37/1.01  
% 3.37/1.01  ------ QBF Options
% 3.37/1.01  
% 3.37/1.01  --qbf_mode                              false
% 3.37/1.01  --qbf_elim_univ                         false
% 3.37/1.01  --qbf_dom_inst                          none
% 3.37/1.01  --qbf_dom_pre_inst                      false
% 3.37/1.01  --qbf_sk_in                             false
% 3.37/1.01  --qbf_pred_elim                         true
% 3.37/1.01  --qbf_split                             512
% 3.37/1.01  
% 3.37/1.01  ------ BMC1 Options
% 3.37/1.01  
% 3.37/1.01  --bmc1_incremental                      false
% 3.37/1.01  --bmc1_axioms                           reachable_all
% 3.37/1.01  --bmc1_min_bound                        0
% 3.37/1.01  --bmc1_max_bound                        -1
% 3.37/1.01  --bmc1_max_bound_default                -1
% 3.37/1.01  --bmc1_symbol_reachability              true
% 3.37/1.01  --bmc1_property_lemmas                  false
% 3.37/1.01  --bmc1_k_induction                      false
% 3.37/1.01  --bmc1_non_equiv_states                 false
% 3.37/1.01  --bmc1_deadlock                         false
% 3.37/1.01  --bmc1_ucm                              false
% 3.37/1.01  --bmc1_add_unsat_core                   none
% 3.37/1.01  --bmc1_unsat_core_children              false
% 3.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.01  --bmc1_out_stat                         full
% 3.37/1.01  --bmc1_ground_init                      false
% 3.37/1.01  --bmc1_pre_inst_next_state              false
% 3.37/1.01  --bmc1_pre_inst_state                   false
% 3.37/1.01  --bmc1_pre_inst_reach_state             false
% 3.37/1.01  --bmc1_out_unsat_core                   false
% 3.37/1.01  --bmc1_aig_witness_out                  false
% 3.37/1.01  --bmc1_verbose                          false
% 3.37/1.01  --bmc1_dump_clauses_tptp                false
% 3.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.01  --bmc1_dump_file                        -
% 3.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.01  --bmc1_ucm_extend_mode                  1
% 3.37/1.01  --bmc1_ucm_init_mode                    2
% 3.37/1.01  --bmc1_ucm_cone_mode                    none
% 3.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.01  --bmc1_ucm_relax_model                  4
% 3.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.01  --bmc1_ucm_layered_model                none
% 3.37/1.01  --bmc1_ucm_max_lemma_size               10
% 3.37/1.01  
% 3.37/1.01  ------ AIG Options
% 3.37/1.01  
% 3.37/1.01  --aig_mode                              false
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation Options
% 3.37/1.01  
% 3.37/1.01  --instantiation_flag                    true
% 3.37/1.01  --inst_sos_flag                         true
% 3.37/1.01  --inst_sos_phase                        true
% 3.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel_side                     num_symb
% 3.37/1.01  --inst_solver_per_active                1400
% 3.37/1.01  --inst_solver_calls_frac                1.
% 3.37/1.01  --inst_passive_queue_type               priority_queues
% 3.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.01  --inst_passive_queues_freq              [25;2]
% 3.37/1.01  --inst_dismatching                      true
% 3.37/1.01  --inst_eager_unprocessed_to_passive     true
% 3.37/1.01  --inst_prop_sim_given                   true
% 3.37/1.01  --inst_prop_sim_new                     false
% 3.37/1.01  --inst_subs_new                         false
% 3.37/1.01  --inst_eq_res_simp                      false
% 3.37/1.01  --inst_subs_given                       false
% 3.37/1.01  --inst_orphan_elimination               true
% 3.37/1.01  --inst_learning_loop_flag               true
% 3.37/1.01  --inst_learning_start                   3000
% 3.37/1.01  --inst_learning_factor                  2
% 3.37/1.01  --inst_start_prop_sim_after_learn       3
% 3.37/1.01  --inst_sel_renew                        solver
% 3.37/1.01  --inst_lit_activity_flag                true
% 3.37/1.01  --inst_restr_to_given                   false
% 3.37/1.01  --inst_activity_threshold               500
% 3.37/1.01  --inst_out_proof                        true
% 3.37/1.01  
% 3.37/1.01  ------ Resolution Options
% 3.37/1.01  
% 3.37/1.01  --resolution_flag                       true
% 3.37/1.01  --res_lit_sel                           adaptive
% 3.37/1.01  --res_lit_sel_side                      none
% 3.37/1.01  --res_ordering                          kbo
% 3.37/1.01  --res_to_prop_solver                    active
% 3.37/1.01  --res_prop_simpl_new                    false
% 3.37/1.01  --res_prop_simpl_given                  true
% 3.37/1.01  --res_passive_queue_type                priority_queues
% 3.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.01  --res_passive_queues_freq               [15;5]
% 3.37/1.01  --res_forward_subs                      full
% 3.37/1.01  --res_backward_subs                     full
% 3.37/1.01  --res_forward_subs_resolution           true
% 3.37/1.01  --res_backward_subs_resolution          true
% 3.37/1.01  --res_orphan_elimination                true
% 3.37/1.01  --res_time_limit                        2.
% 3.37/1.01  --res_out_proof                         true
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Options
% 3.37/1.01  
% 3.37/1.01  --superposition_flag                    true
% 3.37/1.01  --sup_passive_queue_type                priority_queues
% 3.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.01  --demod_completeness_check              fast
% 3.37/1.01  --demod_use_ground                      true
% 3.37/1.01  --sup_to_prop_solver                    passive
% 3.37/1.01  --sup_prop_simpl_new                    true
% 3.37/1.01  --sup_prop_simpl_given                  true
% 3.37/1.01  --sup_fun_splitting                     true
% 3.37/1.01  --sup_smt_interval                      50000
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Simplification Setup
% 3.37/1.01  
% 3.37/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.01  --sup_immed_triv                        [TrivRules]
% 3.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_bw_main                     []
% 3.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_input_bw                          []
% 3.37/1.01  
% 3.37/1.01  ------ Combination Options
% 3.37/1.01  
% 3.37/1.01  --comb_res_mult                         3
% 3.37/1.01  --comb_sup_mult                         2
% 3.37/1.01  --comb_inst_mult                        10
% 3.37/1.01  
% 3.37/1.01  ------ Debug Options
% 3.37/1.01  
% 3.37/1.01  --dbg_backtrace                         false
% 3.37/1.01  --dbg_dump_prop_clauses                 false
% 3.37/1.01  --dbg_dump_prop_clauses_file            -
% 3.37/1.01  --dbg_out_stat                          false
% 3.37/1.01  ------ Parsing...
% 3.37/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.01  ------ Proving...
% 3.37/1.01  ------ Problem Properties 
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  clauses                                 22
% 3.37/1.01  conjectures                             1
% 3.37/1.01  EPR                                     1
% 3.37/1.01  Horn                                    16
% 3.37/1.01  unary                                   4
% 3.37/1.01  binary                                  5
% 3.37/1.01  lits                                    60
% 3.37/1.01  lits eq                                 5
% 3.37/1.01  fd_pure                                 0
% 3.37/1.01  fd_pseudo                               0
% 3.37/1.01  fd_cond                                 0
% 3.37/1.01  fd_pseudo_cond                          3
% 3.37/1.01  AC symbols                              0
% 3.37/1.01  
% 3.37/1.01  ------ Schedule dynamic 5 is on 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  Current options:
% 3.37/1.01  ------ 
% 3.37/1.01  
% 3.37/1.01  ------ Input Options
% 3.37/1.01  
% 3.37/1.01  --out_options                           all
% 3.37/1.01  --tptp_safe_out                         true
% 3.37/1.01  --problem_path                          ""
% 3.37/1.01  --include_path                          ""
% 3.37/1.01  --clausifier                            res/vclausify_rel
% 3.37/1.01  --clausifier_options                    ""
% 3.37/1.01  --stdin                                 false
% 3.37/1.01  --stats_out                             all
% 3.37/1.01  
% 3.37/1.01  ------ General Options
% 3.37/1.01  
% 3.37/1.01  --fof                                   false
% 3.37/1.01  --time_out_real                         305.
% 3.37/1.01  --time_out_virtual                      -1.
% 3.37/1.01  --symbol_type_check                     false
% 3.37/1.01  --clausify_out                          false
% 3.37/1.01  --sig_cnt_out                           false
% 3.37/1.01  --trig_cnt_out                          false
% 3.37/1.01  --trig_cnt_out_tolerance                1.
% 3.37/1.01  --trig_cnt_out_sk_spl                   false
% 3.37/1.01  --abstr_cl_out                          false
% 3.37/1.01  
% 3.37/1.01  ------ Global Options
% 3.37/1.01  
% 3.37/1.01  --schedule                              default
% 3.37/1.01  --add_important_lit                     false
% 3.37/1.01  --prop_solver_per_cl                    1000
% 3.37/1.01  --min_unsat_core                        false
% 3.37/1.01  --soft_assumptions                      false
% 3.37/1.01  --soft_lemma_size                       3
% 3.37/1.01  --prop_impl_unit_size                   0
% 3.37/1.01  --prop_impl_unit                        []
% 3.37/1.01  --share_sel_clauses                     true
% 3.37/1.01  --reset_solvers                         false
% 3.37/1.01  --bc_imp_inh                            [conj_cone]
% 3.37/1.01  --conj_cone_tolerance                   3.
% 3.37/1.01  --extra_neg_conj                        none
% 3.37/1.01  --large_theory_mode                     true
% 3.37/1.01  --prolific_symb_bound                   200
% 3.37/1.01  --lt_threshold                          2000
% 3.37/1.01  --clause_weak_htbl                      true
% 3.37/1.01  --gc_record_bc_elim                     false
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing Options
% 3.37/1.01  
% 3.37/1.01  --preprocessing_flag                    true
% 3.37/1.01  --time_out_prep_mult                    0.1
% 3.37/1.01  --splitting_mode                        input
% 3.37/1.01  --splitting_grd                         true
% 3.37/1.01  --splitting_cvd                         false
% 3.37/1.01  --splitting_cvd_svl                     false
% 3.37/1.01  --splitting_nvd                         32
% 3.37/1.01  --sub_typing                            true
% 3.37/1.01  --prep_gs_sim                           true
% 3.37/1.01  --prep_unflatten                        true
% 3.37/1.01  --prep_res_sim                          true
% 3.37/1.01  --prep_upred                            true
% 3.37/1.01  --prep_sem_filter                       exhaustive
% 3.37/1.01  --prep_sem_filter_out                   false
% 3.37/1.01  --pred_elim                             true
% 3.37/1.01  --res_sim_input                         true
% 3.37/1.01  --eq_ax_congr_red                       true
% 3.37/1.01  --pure_diseq_elim                       true
% 3.37/1.01  --brand_transform                       false
% 3.37/1.01  --non_eq_to_eq                          false
% 3.37/1.01  --prep_def_merge                        true
% 3.37/1.01  --prep_def_merge_prop_impl              false
% 3.37/1.01  --prep_def_merge_mbd                    true
% 3.37/1.01  --prep_def_merge_tr_red                 false
% 3.37/1.01  --prep_def_merge_tr_cl                  false
% 3.37/1.01  --smt_preprocessing                     true
% 3.37/1.01  --smt_ac_axioms                         fast
% 3.37/1.01  --preprocessed_out                      false
% 3.37/1.01  --preprocessed_stats                    false
% 3.37/1.01  
% 3.37/1.01  ------ Abstraction refinement Options
% 3.37/1.01  
% 3.37/1.01  --abstr_ref                             []
% 3.37/1.01  --abstr_ref_prep                        false
% 3.37/1.01  --abstr_ref_until_sat                   false
% 3.37/1.01  --abstr_ref_sig_restrict                funpre
% 3.37/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.01  --abstr_ref_under                       []
% 3.37/1.01  
% 3.37/1.01  ------ SAT Options
% 3.37/1.01  
% 3.37/1.01  --sat_mode                              false
% 3.37/1.01  --sat_fm_restart_options                ""
% 3.37/1.01  --sat_gr_def                            false
% 3.37/1.01  --sat_epr_types                         true
% 3.37/1.01  --sat_non_cyclic_types                  false
% 3.37/1.01  --sat_finite_models                     false
% 3.37/1.01  --sat_fm_lemmas                         false
% 3.37/1.01  --sat_fm_prep                           false
% 3.37/1.01  --sat_fm_uc_incr                        true
% 3.37/1.01  --sat_out_model                         small
% 3.37/1.01  --sat_out_clauses                       false
% 3.37/1.01  
% 3.37/1.01  ------ QBF Options
% 3.37/1.01  
% 3.37/1.01  --qbf_mode                              false
% 3.37/1.01  --qbf_elim_univ                         false
% 3.37/1.01  --qbf_dom_inst                          none
% 3.37/1.01  --qbf_dom_pre_inst                      false
% 3.37/1.01  --qbf_sk_in                             false
% 3.37/1.01  --qbf_pred_elim                         true
% 3.37/1.01  --qbf_split                             512
% 3.37/1.01  
% 3.37/1.01  ------ BMC1 Options
% 3.37/1.01  
% 3.37/1.01  --bmc1_incremental                      false
% 3.37/1.01  --bmc1_axioms                           reachable_all
% 3.37/1.01  --bmc1_min_bound                        0
% 3.37/1.01  --bmc1_max_bound                        -1
% 3.37/1.01  --bmc1_max_bound_default                -1
% 3.37/1.01  --bmc1_symbol_reachability              true
% 3.37/1.01  --bmc1_property_lemmas                  false
% 3.37/1.01  --bmc1_k_induction                      false
% 3.37/1.01  --bmc1_non_equiv_states                 false
% 3.37/1.01  --bmc1_deadlock                         false
% 3.37/1.01  --bmc1_ucm                              false
% 3.37/1.01  --bmc1_add_unsat_core                   none
% 3.37/1.01  --bmc1_unsat_core_children              false
% 3.37/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.01  --bmc1_out_stat                         full
% 3.37/1.01  --bmc1_ground_init                      false
% 3.37/1.01  --bmc1_pre_inst_next_state              false
% 3.37/1.01  --bmc1_pre_inst_state                   false
% 3.37/1.01  --bmc1_pre_inst_reach_state             false
% 3.37/1.01  --bmc1_out_unsat_core                   false
% 3.37/1.01  --bmc1_aig_witness_out                  false
% 3.37/1.01  --bmc1_verbose                          false
% 3.37/1.01  --bmc1_dump_clauses_tptp                false
% 3.37/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.01  --bmc1_dump_file                        -
% 3.37/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.01  --bmc1_ucm_extend_mode                  1
% 3.37/1.01  --bmc1_ucm_init_mode                    2
% 3.37/1.01  --bmc1_ucm_cone_mode                    none
% 3.37/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.01  --bmc1_ucm_relax_model                  4
% 3.37/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.01  --bmc1_ucm_layered_model                none
% 3.37/1.01  --bmc1_ucm_max_lemma_size               10
% 3.37/1.01  
% 3.37/1.01  ------ AIG Options
% 3.37/1.01  
% 3.37/1.01  --aig_mode                              false
% 3.37/1.01  
% 3.37/1.01  ------ Instantiation Options
% 3.37/1.01  
% 3.37/1.01  --instantiation_flag                    true
% 3.37/1.01  --inst_sos_flag                         true
% 3.37/1.01  --inst_sos_phase                        true
% 3.37/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.01  --inst_lit_sel_side                     none
% 3.37/1.01  --inst_solver_per_active                1400
% 3.37/1.01  --inst_solver_calls_frac                1.
% 3.37/1.01  --inst_passive_queue_type               priority_queues
% 3.37/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.01  --inst_passive_queues_freq              [25;2]
% 3.37/1.01  --inst_dismatching                      true
% 3.37/1.01  --inst_eager_unprocessed_to_passive     true
% 3.37/1.01  --inst_prop_sim_given                   true
% 3.37/1.01  --inst_prop_sim_new                     false
% 3.37/1.01  --inst_subs_new                         false
% 3.37/1.01  --inst_eq_res_simp                      false
% 3.37/1.01  --inst_subs_given                       false
% 3.37/1.01  --inst_orphan_elimination               true
% 3.37/1.01  --inst_learning_loop_flag               true
% 3.37/1.01  --inst_learning_start                   3000
% 3.37/1.01  --inst_learning_factor                  2
% 3.37/1.01  --inst_start_prop_sim_after_learn       3
% 3.37/1.01  --inst_sel_renew                        solver
% 3.37/1.01  --inst_lit_activity_flag                true
% 3.37/1.01  --inst_restr_to_given                   false
% 3.37/1.01  --inst_activity_threshold               500
% 3.37/1.01  --inst_out_proof                        true
% 3.37/1.01  
% 3.37/1.01  ------ Resolution Options
% 3.37/1.01  
% 3.37/1.01  --resolution_flag                       false
% 3.37/1.01  --res_lit_sel                           adaptive
% 3.37/1.01  --res_lit_sel_side                      none
% 3.37/1.01  --res_ordering                          kbo
% 3.37/1.01  --res_to_prop_solver                    active
% 3.37/1.01  --res_prop_simpl_new                    false
% 3.37/1.01  --res_prop_simpl_given                  true
% 3.37/1.01  --res_passive_queue_type                priority_queues
% 3.37/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.01  --res_passive_queues_freq               [15;5]
% 3.37/1.01  --res_forward_subs                      full
% 3.37/1.01  --res_backward_subs                     full
% 3.37/1.01  --res_forward_subs_resolution           true
% 3.37/1.01  --res_backward_subs_resolution          true
% 3.37/1.01  --res_orphan_elimination                true
% 3.37/1.01  --res_time_limit                        2.
% 3.37/1.01  --res_out_proof                         true
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Options
% 3.37/1.01  
% 3.37/1.01  --superposition_flag                    true
% 3.37/1.01  --sup_passive_queue_type                priority_queues
% 3.37/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.01  --demod_completeness_check              fast
% 3.37/1.01  --demod_use_ground                      true
% 3.37/1.01  --sup_to_prop_solver                    passive
% 3.37/1.01  --sup_prop_simpl_new                    true
% 3.37/1.01  --sup_prop_simpl_given                  true
% 3.37/1.01  --sup_fun_splitting                     true
% 3.37/1.01  --sup_smt_interval                      50000
% 3.37/1.01  
% 3.37/1.01  ------ Superposition Simplification Setup
% 3.37/1.01  
% 3.37/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.01  --sup_immed_triv                        [TrivRules]
% 3.37/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_immed_bw_main                     []
% 3.37/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.01  --sup_input_bw                          []
% 3.37/1.01  
% 3.37/1.01  ------ Combination Options
% 3.37/1.01  
% 3.37/1.01  --comb_res_mult                         3
% 3.37/1.01  --comb_sup_mult                         2
% 3.37/1.01  --comb_inst_mult                        10
% 3.37/1.01  
% 3.37/1.01  ------ Debug Options
% 3.37/1.01  
% 3.37/1.01  --dbg_backtrace                         false
% 3.37/1.01  --dbg_dump_prop_clauses                 false
% 3.37/1.01  --dbg_dump_prop_clauses_file            -
% 3.37/1.01  --dbg_out_stat                          false
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ Proving...
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS status Theorem for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  fof(f2,axiom,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f14,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f2])).
% 3.37/1.01  
% 3.37/1.01  fof(f15,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f14])).
% 3.37/1.01  
% 3.37/1.01  fof(f32,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(nnf_transformation,[],[f15])).
% 3.37/1.01  
% 3.37/1.01  fof(f33,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(rectify,[],[f32])).
% 3.37/1.01  
% 3.37/1.01  fof(f34,plain,(
% 3.37/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f35,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.37/1.01  
% 3.37/1.01  fof(f55,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f35])).
% 3.37/1.01  
% 3.37/1.01  fof(f10,conjecture,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f11,negated_conjecture,(
% 3.37/1.01    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.37/1.01    inference(negated_conjecture,[],[f10])).
% 3.37/1.01  
% 3.37/1.01  fof(f30,plain,(
% 3.37/1.01    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f11])).
% 3.37/1.01  
% 3.37/1.01  fof(f31,plain,(
% 3.37/1.01    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f30])).
% 3.37/1.01  
% 3.37/1.01  fof(f50,plain,(
% 3.37/1.01    ( ! [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5)) | ~r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6))) & r1_tarski(sK5,sK6))) )),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f49,plain,(
% 3.37/1.01    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1)) | ~r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f51,plain,(
% 3.37/1.01    ((~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))) & r1_tarski(sK5,sK6)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f50,f49])).
% 3.37/1.01  
% 3.37/1.01  fof(f77,plain,(
% 3.37/1.01    l3_lattices(sK4)),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f74,plain,(
% 3.37/1.01    ~v2_struct_0(sK4)),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f3,axiom,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f16,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f3])).
% 3.37/1.01  
% 3.37/1.01  fof(f17,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f16])).
% 3.37/1.01  
% 3.37/1.01  fof(f36,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(nnf_transformation,[],[f17])).
% 3.37/1.01  
% 3.37/1.01  fof(f37,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(rectify,[],[f36])).
% 3.37/1.01  
% 3.37/1.01  fof(f38,plain,(
% 3.37/1.01    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f39,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.37/1.01  
% 3.37/1.01  fof(f59,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f39])).
% 3.37/1.01  
% 3.37/1.01  fof(f1,axiom,(
% 3.37/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f12,plain,(
% 3.37/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.37/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 3.37/1.01  
% 3.37/1.01  fof(f13,plain,(
% 3.37/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.37/1.01    inference(ennf_transformation,[],[f12])).
% 3.37/1.01  
% 3.37/1.01  fof(f52,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f13])).
% 3.37/1.01  
% 3.37/1.01  fof(f78,plain,(
% 3.37/1.01    r1_tarski(sK5,sK6)),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f6,axiom,(
% 3.37/1.01    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f22,plain,(
% 3.37/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.37/1.01    inference(ennf_transformation,[],[f6])).
% 3.37/1.01  
% 3.37/1.01  fof(f23,plain,(
% 3.37/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.37/1.01    inference(flattening,[],[f22])).
% 3.37/1.01  
% 3.37/1.01  fof(f40,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.37/1.01    inference(nnf_transformation,[],[f23])).
% 3.37/1.01  
% 3.37/1.01  fof(f41,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.37/1.01    inference(rectify,[],[f40])).
% 3.37/1.01  
% 3.37/1.01  fof(f42,plain,(
% 3.37/1.01    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f43,plain,(
% 3.37/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 3.37/1.01  
% 3.37/1.01  fof(f64,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f43])).
% 3.37/1.01  
% 3.37/1.01  fof(f76,plain,(
% 3.37/1.01    v4_lattice3(sK4)),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f75,plain,(
% 3.37/1.01    v10_lattices(sK4)),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f8,axiom,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f26,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f8])).
% 3.37/1.01  
% 3.37/1.01  fof(f27,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f26])).
% 3.37/1.01  
% 3.37/1.01  fof(f72,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f27])).
% 3.37/1.01  
% 3.37/1.01  fof(f7,axiom,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f24,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f7])).
% 3.37/1.01  
% 3.37/1.01  fof(f25,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f24])).
% 3.37/1.01  
% 3.37/1.01  fof(f44,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(nnf_transformation,[],[f25])).
% 3.37/1.01  
% 3.37/1.01  fof(f45,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f44])).
% 3.37/1.01  
% 3.37/1.01  fof(f46,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(rectify,[],[f45])).
% 3.37/1.01  
% 3.37/1.01  fof(f47,plain,(
% 3.37/1.01    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f48,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 3.37/1.01  
% 3.37/1.01  fof(f68,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f48])).
% 3.37/1.01  
% 3.37/1.01  fof(f81,plain,(
% 3.37/1.01    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f68])).
% 3.37/1.01  
% 3.37/1.01  fof(f9,axiom,(
% 3.37/1.01    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f28,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f9])).
% 3.37/1.01  
% 3.37/1.01  fof(f29,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f28])).
% 3.37/1.01  
% 3.37/1.01  fof(f73,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f29])).
% 3.37/1.01  
% 3.37/1.01  fof(f79,plain,(
% 3.37/1.01    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))),
% 3.37/1.01    inference(cnf_transformation,[],[f51])).
% 3.37/1.01  
% 3.37/1.01  fof(f4,axiom,(
% 3.37/1.01    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f18,plain,(
% 3.37/1.01    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f4])).
% 3.37/1.01  
% 3.37/1.01  fof(f19,plain,(
% 3.37/1.01    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f18])).
% 3.37/1.01  
% 3.37/1.01  fof(f61,plain,(
% 3.37/1.01    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f19])).
% 3.37/1.01  
% 3.37/1.01  fof(f5,axiom,(
% 3.37/1.01    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.37/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f20,plain,(
% 3.37/1.01    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f5])).
% 3.37/1.01  
% 3.37/1.01  fof(f21,plain,(
% 3.37/1.01    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.37/1.01    inference(flattening,[],[f20])).
% 3.37/1.01  
% 3.37/1.01  fof(f62,plain,(
% 3.37/1.01    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f21])).
% 3.37/1.01  
% 3.37/1.01  fof(f67,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f48])).
% 3.37/1.01  
% 3.37/1.01  fof(f82,plain,(
% 3.37/1.01    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f67])).
% 3.37/1.01  
% 3.37/1.01  fof(f53,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f35])).
% 3.37/1.01  
% 3.37/1.01  fof(f56,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f35])).
% 3.37/1.02  
% 3.37/1.02  fof(f54,plain,(
% 3.37/1.02    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f35])).
% 3.37/1.02  
% 3.37/1.02  fof(f58,plain,(
% 3.37/1.02    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f39])).
% 3.37/1.02  
% 3.37/1.02  fof(f65,plain,(
% 3.37/1.02    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK2(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f43])).
% 3.37/1.02  
% 3.37/1.02  fof(f63,plain,(
% 3.37/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f43])).
% 3.37/1.02  
% 3.37/1.02  fof(f57,plain,(
% 3.37/1.02    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f39])).
% 3.37/1.02  
% 3.37/1.02  fof(f60,plain,(
% 3.37/1.02    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f39])).
% 3.37/1.02  
% 3.37/1.02  fof(f66,plain,(
% 3.37/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.37/1.02    inference(cnf_transformation,[],[f43])).
% 3.37/1.02  
% 3.37/1.02  fof(f80,plain,(
% 3.37/1.02    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.37/1.02    inference(equality_resolution,[],[f66])).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2,plain,
% 3.37/1.02      ( r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_24,negated_conjecture,
% 3.37/1.02      ( l3_lattices(sK4) ),
% 3.37/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_861,plain,
% 3.37/1.02      ( r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_862,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_861]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_27,negated_conjecture,
% 3.37/1.02      ( ~ v2_struct_0(sK4) ),
% 3.37/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_866,plain,
% 3.37/1.02      ( r2_hidden(sK0(sK4,X0,X1),X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r3_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_862,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_867,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK0(sK4,X0,X1),X1) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_866]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1617,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK0(sK4,X0_51,X0_52),X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_867]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2091,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0_51,X0_52) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,X0_51,X0_52),X0_52) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_6,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_771,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_772,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_771]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_776,plain,
% 3.37/1.02      ( r2_hidden(sK1(sK4,X0,X1),X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r4_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_772,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_777,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK1(sK4,X0,X1),X1) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_776]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1621,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(sK1(sK4,X0_51,X0_52),X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_777]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2087,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,X0_51,X0_52),X0_52) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1621]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_0,plain,
% 3.37/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.37/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_23,negated_conjecture,
% 3.37/1.02      ( r1_tarski(sK5,sK6) ),
% 3.37/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_315,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK5 != X1 | sK6 != X2 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_316,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,sK5) | r2_hidden(X0,sK6) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_315]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1636,plain,
% 3.37/1.02      ( ~ r2_hidden(X0_51,sK5) | r2_hidden(X0_51,sK6) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_316]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2073,plain,
% 3.37/1.02      ( r2_hidden(X0_51,sK5) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,sK6) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2905,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,sK5) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,X0_51,sK5),sK6) = iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2087,c_2073]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_13,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.37/1.02      | ~ v10_lattices(X1)
% 3.37/1.02      | ~ v4_lattice3(X1)
% 3.37/1.02      | v2_struct_0(X1)
% 3.37/1.02      | ~ l3_lattices(X1)
% 3.37/1.02      | sK2(X0,X1,X2) = X0 ),
% 3.37/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_25,negated_conjecture,
% 3.37/1.02      ( v4_lattice3(sK4) ),
% 3.37/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_482,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.37/1.02      | ~ v10_lattices(X1)
% 3.37/1.02      | v2_struct_0(X1)
% 3.37/1.02      | ~ l3_lattices(X1)
% 3.37/1.02      | sK2(X0,X1,X2) = X0
% 3.37/1.02      | sK4 != X1 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_483,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4)
% 3.37/1.02      | sK2(X0,sK4,X1) = X0 ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_482]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_26,negated_conjecture,
% 3.37/1.02      ( v10_lattices(sK4) ),
% 3.37/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_487,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) | sK2(X0,sK4,X1) = X0 ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_483,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1634,plain,
% 3.37/1.02      ( ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52))
% 3.37/1.02      | sK2(X0_51,sK4,X0_52) = X0_51 ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_487]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2075,plain,
% 3.37/1.02      ( sK2(X0_51,sK4,X0_52) = X0_51
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3688,plain,
% 3.37/1.02      ( sK2(sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)),sK4,X0_52) = sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52))
% 3.37/1.02      | r3_lattice3(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2091,c_2075]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_20,plain,
% 3.37/1.02      ( ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 3.37/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_536,plain,
% 3.37/1.02      ( ~ v10_lattices(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_537,plain,
% 3.37/1.02      ( ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4)
% 3.37/1.02      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_536]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_541,plain,
% 3.37/1.02      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_537,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1631,plain,
% 3.37/1.02      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)) = k15_lattice3(sK4,X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_541]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_18,plain,
% 3.37/1.02      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_21,plain,
% 3.37/1.02      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_168,plain,
% 3.37/1.02      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X2)
% 3.37/1.02      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_18,c_21]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_169,plain,
% 3.37/1.02      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_168]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_515,plain,
% 3.37/1.02      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_169,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_516,plain,
% 3.37/1.02      ( r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_515]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_520,plain,
% 3.37/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_516,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_521,plain,
% 3.37/1.02      ( r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_520]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1632,plain,
% 3.37/1.02      ( r3_lattices(sK4,X0_51,k16_lattice3(sK4,X0_52))
% 3.37/1.02      | ~ r3_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_521]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2077,plain,
% 3.37/1.02      ( r3_lattices(sK4,X0_51,k16_lattice3(sK4,X0_52)) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,X0_51,X0_52) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2913,plain,
% 3.37/1.02      ( r3_lattices(sK4,X0_51,k15_lattice3(sK4,X0_52)) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_1631,c_2077]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5237,plain,
% 3.37/1.02      ( sK2(sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52)),sK4,X0_52) = sK0(sK4,X0_51,a_2_2_lattice3(sK4,X0_52))
% 3.37/1.02      | r3_lattices(sK4,X0_51,k15_lattice3(sK4,X0_52)) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_3688,c_2913]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_22,negated_conjecture,
% 3.37/1.02      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 3.37/1.02      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 3.37/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1637,negated_conjecture,
% 3.37/1.02      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 3.37/1.02      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2072,plain,
% 3.37/1.02      ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
% 3.37/1.02      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2914,plain,
% 3.37/1.02      ( r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.37/1.02      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2077,c_2072]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5259,plain,
% 3.37/1.02      ( sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6))
% 3.37/1.02      | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.37/1.02      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_5237,c_2914]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_9,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_708,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_709,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_708]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_713,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_709,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1624,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_713]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1690,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1692,plain,
% 3.37/1.02      ( m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(instantiation,[status(thm)],[c_1690]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_10,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_693,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_694,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_693]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_698,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_694,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1625,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_698]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3223,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(instantiation,[status(thm)],[c_1625]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3224,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_3223]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3689,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0_51,sK5) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,X0_51,sK5),sK6) = iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2091,c_2073]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_19,plain,
% 3.37/1.02      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.37/1.02      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_161,plain,
% 3.37/1.02      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_19,c_10]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_500,plain,
% 3.37/1.02      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_161,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_501,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0)
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_500]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_505,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0),X0) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_501,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1633,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_505]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2076,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X0_52) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2083,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_4,plain,
% 3.37/1.02      ( r1_lattices(X0,X1,X2)
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X3)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.02      | ~ r2_hidden(X2,X3)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_813,plain,
% 3.37/1.02      ( r1_lattices(X0,X1,X2)
% 3.37/1.02      | ~ r3_lattice3(X0,X1,X3)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.37/1.02      | ~ r2_hidden(X2,X3)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_814,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0,X1)
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X2)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X1,X2)
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_813]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_818,plain,
% 3.37/1.02      ( ~ r2_hidden(X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X2)
% 3.37/1.02      | r1_lattices(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_814,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_819,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0,X1)
% 3.37/1.02      | ~ r3_lattice3(sK4,X0,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X1,X2) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_818]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1619,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0_51,X1_51)
% 3.37/1.02      | ~ r3_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X1_51,X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_819]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2089,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0_51,X1_51) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,X0_51,X0_52) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X1_51,X0_52) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3294,plain,
% 3.37/1.02      ( r1_lattices(sK4,k16_lattice3(sK4,X0_52),X0_51) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,X1_52) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2083,c_2089]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_4797,plain,
% 3.37/1.02      ( r1_lattices(sK4,k16_lattice3(sK4,X0_52),X0_51) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,X0_52) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2076,c_3294]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1,plain,
% 3.37/1.02      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.37/1.02      | r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_882,plain,
% 3.37/1.02      ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.37/1.02      | r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_883,plain,
% 3.37/1.02      ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.37/1.02      | r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_882]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_887,plain,
% 3.37/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_883,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_888,plain,
% 3.37/1.02      ( ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.37/1.02      | r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_887]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1616,plain,
% 3.37/1.02      ( ~ r1_lattices(sK4,X0_51,sK0(sK4,X0_51,X0_52))
% 3.37/1.02      | r3_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_888]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2092,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0_51,sK0(sK4,X0_51,X0_52)) != iProver_top
% 3.37/1.02      | r3_lattice3(sK4,X0_51,X0_52) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_4979,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_4797,c_2092]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1687,plain,
% 3.37/1.02      ( m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3,plain,
% 3.37/1.02      ( r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_840,plain,
% 3.37/1.02      ( r3_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_841,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_840]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_845,plain,
% 3.37/1.02      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r3_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_841,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_846,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_845]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1618,plain,
% 3.37/1.02      ( r3_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK0(sK4,X0_51,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_846]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2151,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52)
% 3.37/1.02      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(instantiation,[status(thm)],[c_1618]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2152,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) = iProver_top
% 3.37/1.02      | m1_subset_1(k16_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_2151]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5022,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_4979,c_1687,c_2152]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5028,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 3.37/1.02      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_3689,c_5022]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5404,plain,
% 3.37/1.02      ( sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6) = sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_5259,c_1692,c_3224,c_5028]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_7,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_750,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_751,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_750]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_755,plain,
% 3.37/1.02      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r4_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_751,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_756,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_755]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1622,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | m1_subset_1(sK1(sK4,X0_51,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_756]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2086,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(sK1(sK4,X0_51,X0_52),u1_struct_0(sK4)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_12,plain,
% 3.37/1.02      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.37/1.02      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_619,plain,
% 3.37/1.02      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.37/1.02      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_620,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_619]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_624,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | r4_lattice3(sK4,sK2(X0,sK4,X1),X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_620,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_625,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0,sK4,X1),X1)
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_624]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1627,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X0_52)
% 3.37/1.02      | ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_625]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2081,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X0_52) = iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_14,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.37/1.02      | ~ v10_lattices(X1)
% 3.37/1.02      | ~ v4_lattice3(X1)
% 3.37/1.02      | v2_struct_0(X1)
% 3.37/1.02      | ~ l3_lattices(X1) ),
% 3.37/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_464,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.37/1.02      | ~ v10_lattices(X1)
% 3.37/1.02      | v2_struct_0(X1)
% 3.37/1.02      | ~ l3_lattices(X1)
% 3.37/1.02      | sK4 != X1 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_465,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_464]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_469,plain,
% 3.37/1.02      ( ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_465,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_470,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0,sK4,X1),u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_469]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1635,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_470]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2074,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) = iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_8,plain,
% 3.37/1.02      ( ~ r4_lattice3(X0,X1,X2)
% 3.37/1.02      | r1_lattices(X0,X3,X1)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.37/1.02      | ~ r2_hidden(X3,X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_723,plain,
% 3.37/1.02      ( ~ r4_lattice3(X0,X1,X2)
% 3.37/1.02      | r1_lattices(X0,X3,X1)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.37/1.02      | ~ r2_hidden(X3,X2)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_724,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | r1_lattices(sK4,X2,X0)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X2,X1)
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_723]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_728,plain,
% 3.37/1.02      ( ~ r2_hidden(X2,X1)
% 3.37/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r1_lattices(sK4,X2,X0)
% 3.37/1.02      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_724,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_729,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | r1_lattices(sK4,X2,X0)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X2,X1) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_728]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1623,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | r1_lattices(sK4,X1_51,X0_51)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
% 3.37/1.02      | ~ r2_hidden(X1_51,X0_52) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_729]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2085,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52) != iProver_top
% 3.37/1.02      | r1_lattices(sK4,X1_51,X0_51) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X1_51,X0_52) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_3122,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) != iProver_top
% 3.37/1.02      | r1_lattices(sK4,X1_51,sK2(X0_51,sK4,X0_52)) = iProver_top
% 3.37/1.02      | m1_subset_1(X1_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X1_51,X1_52) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2074,c_2085]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5131,plain,
% 3.37/1.02      ( r1_lattices(sK4,X0_51,sK2(X1_51,sK4,X0_52)) = iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,X0_52) != iProver_top
% 3.37/1.02      | r2_hidden(X1_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2081,c_3122]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_792,plain,
% 3.37/1.02      ( r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_793,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | v2_struct_0(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_792]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_797,plain,
% 3.37/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.37/1.02      | r4_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_793,c_27]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_798,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_797]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1620,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ r1_lattices(sK4,sK1(sK4,X0_51,X0_52),X0_51)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_798]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2088,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52) = iProver_top
% 3.37/1.02      | r1_lattices(sK4,sK1(sK4,X0_51,X0_52),X0_51) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1620]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5140,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | m1_subset_1(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_5131,c_2088]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1659,plain,
% 3.37/1.02      ( m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) = iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5837,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_5140,c_1659]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5841,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK2(X0_51,sK4,X0_52),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2086,c_5837]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5849,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(X0_51,sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) != iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK2(X0_51,sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_5841,c_1659]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5856,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK2(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK4,sK6),X0_52) = iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52),sK6) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_5404,c_5849]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5857,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52) = iProver_top
% 3.37/1.02      | r2_hidden(sK1(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),X0_52),sK6) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(light_normalisation,[status(thm)],[c_5856,c_5404]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_6687,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2905,c_5857]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5409,plain,
% 3.37/1.02      ( m1_subset_1(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),u1_struct_0(sK4)) = iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_5404,c_2074]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_6691,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
% 3.37/1.02      | r2_hidden(sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),a_2_2_lattice3(sK4,sK6)) != iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_6687,c_5409]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_6695,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.37/1.02      | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2091,c_6691]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_9460,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top
% 3.37/1.02      | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_6695,c_1692]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_9461,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)),sK5) = iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_9460]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_11,plain,
% 3.37/1.02      ( ~ r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | ~ v4_lattice3(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0) ),
% 3.37/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_637,plain,
% 3.37/1.02      ( ~ r4_lattice3(X0,X1,X2)
% 3.37/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.37/1.02      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.37/1.02      | ~ v10_lattices(X0)
% 3.37/1.02      | v2_struct_0(X0)
% 3.37/1.02      | ~ l3_lattices(X0)
% 3.37/1.02      | sK4 != X0 ),
% 3.37/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_638,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | ~ v10_lattices(sK4)
% 3.37/1.02      | v2_struct_0(sK4)
% 3.37/1.02      | ~ l3_lattices(sK4) ),
% 3.37/1.02      inference(unflattening,[status(thm)],[c_637]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_642,plain,
% 3.37/1.02      ( r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_638,c_27,c_26,c_24]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_643,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0,X1)
% 3.37/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_642]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_1626,plain,
% 3.37/1.02      ( ~ r4_lattice3(sK4,X0_51,X0_52)
% 3.37/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) ),
% 3.37/1.02      inference(subtyping,[status(esa)],[c_643]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2082,plain,
% 3.37/1.02      ( r4_lattice3(sK4,X0_51,X0_52) != iProver_top
% 3.37/1.02      | m1_subset_1(X0_51,u1_struct_0(sK4)) != iProver_top
% 3.37/1.02      | r2_hidden(X0_51,a_2_2_lattice3(sK4,X0_52)) = iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5027,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52),X0_52) != iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_52)),X1_52),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_2082,c_5022]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5031,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(light_normalisation,[status(thm)],[c_5027,c_1631]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2146,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52)
% 3.37/1.02      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4))
% 3.37/1.02      | ~ m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) ),
% 3.37/1.02      inference(instantiation,[status(thm)],[c_1618]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_2147,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | m1_subset_1(sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),u1_struct_0(sK4)) = iProver_top
% 3.37/1.02      | m1_subset_1(k15_lattice3(sK4,X0_52),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(predicate_to_equality,[status(thm)],[c_2146]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5055,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top
% 3.37/1.02      | r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top ),
% 3.37/1.02      inference(global_propositional_subsumption,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_5031,c_1690,c_2147]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_5056,plain,
% 3.37/1.02      ( r4_lattice3(sK4,sK0(sK4,k15_lattice3(sK4,X0_52),X1_52),X0_52) != iProver_top
% 3.37/1.02      | r3_lattice3(sK4,k15_lattice3(sK4,X0_52),X1_52) = iProver_top ),
% 3.37/1.02      inference(renaming,[status(thm)],[c_5055]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_9474,plain,
% 3.37/1.02      ( r3_lattice3(sK4,k15_lattice3(sK4,sK5),a_2_2_lattice3(sK4,sK6)) = iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_9461,c_5056]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(c_9577,plain,
% 3.37/1.02      ( r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) = iProver_top
% 3.37/1.02      | m1_subset_1(k15_lattice3(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
% 3.37/1.02      inference(superposition,[status(thm)],[c_9474,c_2913]) ).
% 3.37/1.02  
% 3.37/1.02  cnf(contradiction,plain,
% 3.37/1.02      ( $false ),
% 3.37/1.02      inference(minisat,
% 3.37/1.02                [status(thm)],
% 3.37/1.02                [c_9577,c_5028,c_3224,c_2914,c_1692]) ).
% 3.37/1.02  
% 3.37/1.02  
% 3.37/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.02  
% 3.37/1.02  ------                               Statistics
% 3.37/1.02  
% 3.37/1.02  ------ General
% 3.37/1.02  
% 3.37/1.02  abstr_ref_over_cycles:                  0
% 3.37/1.02  abstr_ref_under_cycles:                 0
% 3.37/1.02  gc_basic_clause_elim:                   0
% 3.37/1.02  forced_gc_time:                         0
% 3.37/1.02  parsing_time:                           0.008
% 3.37/1.02  unif_index_cands_time:                  0.
% 3.37/1.02  unif_index_add_time:                    0.
% 3.37/1.02  orderings_time:                         0.
% 3.37/1.02  out_proof_time:                         0.016
% 3.37/1.02  total_time:                             0.317
% 3.37/1.02  num_of_symbols:                         54
% 3.37/1.02  num_of_terms:                           11587
% 3.37/1.02  
% 3.37/1.02  ------ Preprocessing
% 3.37/1.02  
% 3.37/1.02  num_of_splits:                          0
% 3.37/1.02  num_of_split_atoms:                     0
% 3.37/1.02  num_of_reused_defs:                     0
% 3.37/1.02  num_eq_ax_congr_red:                    58
% 3.37/1.02  num_of_sem_filtered_clauses:            1
% 3.37/1.02  num_of_subtypes:                        4
% 3.37/1.02  monotx_restored_types:                  1
% 3.37/1.02  sat_num_of_epr_types:                   0
% 3.37/1.02  sat_num_of_non_cyclic_types:            0
% 3.37/1.02  sat_guarded_non_collapsed_types:        1
% 3.37/1.02  num_pure_diseq_elim:                    0
% 3.37/1.02  simp_replaced_by:                       0
% 3.37/1.02  res_preprocessed:                       110
% 3.37/1.02  prep_upred:                             0
% 3.37/1.02  prep_unflattend:                        58
% 3.37/1.02  smt_new_axioms:                         0
% 3.37/1.02  pred_elim_cands:                        6
% 3.37/1.02  pred_elim:                              5
% 3.37/1.02  pred_elim_cl:                           5
% 3.37/1.02  pred_elim_cycles:                       10
% 3.37/1.02  merged_defs:                            0
% 3.37/1.02  merged_defs_ncl:                        0
% 3.37/1.02  bin_hyper_res:                          0
% 3.37/1.02  prep_cycles:                            4
% 3.37/1.02  pred_elim_time:                         0.014
% 3.37/1.02  splitting_time:                         0.
% 3.37/1.02  sem_filter_time:                        0.
% 3.37/1.02  monotx_time:                            0.
% 3.37/1.02  subtype_inf_time:                       0.001
% 3.37/1.02  
% 3.37/1.02  ------ Problem properties
% 3.37/1.02  
% 3.37/1.02  clauses:                                22
% 3.37/1.02  conjectures:                            1
% 3.37/1.02  epr:                                    1
% 3.37/1.02  horn:                                   16
% 3.37/1.02  ground:                                 1
% 3.37/1.02  unary:                                  4
% 3.37/1.02  binary:                                 5
% 3.37/1.02  lits:                                   60
% 3.37/1.02  lits_eq:                                5
% 3.37/1.02  fd_pure:                                0
% 3.37/1.02  fd_pseudo:                              0
% 3.37/1.02  fd_cond:                                0
% 3.37/1.02  fd_pseudo_cond:                         3
% 3.37/1.02  ac_symbols:                             0
% 3.37/1.02  
% 3.37/1.02  ------ Propositional Solver
% 3.37/1.02  
% 3.37/1.02  prop_solver_calls:                      29
% 3.37/1.02  prop_fast_solver_calls:                 1496
% 3.37/1.02  smt_solver_calls:                       0
% 3.37/1.02  smt_fast_solver_calls:                  0
% 3.37/1.02  prop_num_of_clauses:                    4971
% 3.37/1.02  prop_preprocess_simplified:             9887
% 3.37/1.02  prop_fo_subsumed:                       83
% 3.37/1.02  prop_solver_time:                       0.
% 3.37/1.02  smt_solver_time:                        0.
% 3.37/1.02  smt_fast_solver_time:                   0.
% 3.37/1.02  prop_fast_solver_time:                  0.
% 3.37/1.02  prop_unsat_core_time:                   0.
% 3.37/1.02  
% 3.37/1.02  ------ QBF
% 3.37/1.02  
% 3.37/1.02  qbf_q_res:                              0
% 3.37/1.02  qbf_num_tautologies:                    0
% 3.37/1.02  qbf_prep_cycles:                        0
% 3.37/1.02  
% 3.37/1.02  ------ BMC1
% 3.37/1.02  
% 3.37/1.02  bmc1_current_bound:                     -1
% 3.37/1.02  bmc1_last_solved_bound:                 -1
% 3.37/1.02  bmc1_unsat_core_size:                   -1
% 3.37/1.02  bmc1_unsat_core_parents_size:           -1
% 3.37/1.02  bmc1_merge_next_fun:                    0
% 3.37/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.02  
% 3.37/1.02  ------ Instantiation
% 3.37/1.02  
% 3.37/1.02  inst_num_of_clauses:                    1042
% 3.37/1.02  inst_num_in_passive:                    517
% 3.37/1.02  inst_num_in_active:                     257
% 3.37/1.02  inst_num_in_unprocessed:                268
% 3.37/1.02  inst_num_of_loops:                      580
% 3.37/1.02  inst_num_of_learning_restarts:          0
% 3.37/1.02  inst_num_moves_active_passive:          322
% 3.37/1.02  inst_lit_activity:                      0
% 3.37/1.02  inst_lit_activity_moves:                1
% 3.37/1.02  inst_num_tautologies:                   0
% 3.37/1.02  inst_num_prop_implied:                  0
% 3.37/1.02  inst_num_existing_simplified:           0
% 3.37/1.02  inst_num_eq_res_simplified:             0
% 3.37/1.02  inst_num_child_elim:                    0
% 3.37/1.02  inst_num_of_dismatching_blockings:      471
% 3.37/1.02  inst_num_of_non_proper_insts:           881
% 3.37/1.02  inst_num_of_duplicates:                 0
% 3.37/1.02  inst_inst_num_from_inst_to_res:         0
% 3.37/1.02  inst_dismatching_checking_time:         0.
% 3.37/1.02  
% 3.37/1.02  ------ Resolution
% 3.37/1.02  
% 3.37/1.02  res_num_of_clauses:                     0
% 3.37/1.02  res_num_in_passive:                     0
% 3.37/1.02  res_num_in_active:                      0
% 3.37/1.02  res_num_of_loops:                       114
% 3.37/1.02  res_forward_subset_subsumed:            16
% 3.37/1.02  res_backward_subset_subsumed:           0
% 3.37/1.02  res_forward_subsumed:                   0
% 3.37/1.02  res_backward_subsumed:                  0
% 3.37/1.02  res_forward_subsumption_resolution:     5
% 3.37/1.02  res_backward_subsumption_resolution:    0
% 3.37/1.02  res_clause_to_clause_subsumption:       1168
% 3.37/1.02  res_orphan_elimination:                 0
% 3.37/1.02  res_tautology_del:                      51
% 3.37/1.02  res_num_eq_res_simplified:              0
% 3.37/1.02  res_num_sel_changes:                    0
% 3.37/1.02  res_moves_from_active_to_pass:          0
% 3.37/1.02  
% 3.37/1.02  ------ Superposition
% 3.37/1.02  
% 3.37/1.02  sup_time_total:                         0.
% 3.37/1.02  sup_time_generating:                    0.
% 3.37/1.02  sup_time_sim_full:                      0.
% 3.37/1.02  sup_time_sim_immed:                     0.
% 3.37/1.02  
% 3.37/1.02  sup_num_of_clauses:                     205
% 3.37/1.02  sup_num_in_active:                      104
% 3.37/1.02  sup_num_in_passive:                     101
% 3.37/1.02  sup_num_of_loops:                       115
% 3.37/1.02  sup_fw_superposition:                   164
% 3.37/1.02  sup_bw_superposition:                   98
% 3.37/1.02  sup_immediate_simplified:               62
% 3.37/1.02  sup_given_eliminated:                   8
% 3.37/1.02  comparisons_done:                       0
% 3.37/1.02  comparisons_avoided:                    11
% 3.37/1.02  
% 3.37/1.02  ------ Simplifications
% 3.37/1.02  
% 3.37/1.02  
% 3.37/1.02  sim_fw_subset_subsumed:                 14
% 3.37/1.02  sim_bw_subset_subsumed:                 1
% 3.37/1.02  sim_fw_subsumed:                        18
% 3.37/1.02  sim_bw_subsumed:                        18
% 3.37/1.02  sim_fw_subsumption_res:                 0
% 3.37/1.02  sim_bw_subsumption_res:                 0
% 3.37/1.02  sim_tautology_del:                      2
% 3.37/1.02  sim_eq_tautology_del:                   11
% 3.37/1.02  sim_eq_res_simp:                        0
% 3.37/1.02  sim_fw_demodulated:                     4
% 3.37/1.02  sim_bw_demodulated:                     0
% 3.37/1.02  sim_light_normalised:                   36
% 3.37/1.02  sim_joinable_taut:                      0
% 3.37/1.02  sim_joinable_simp:                      0
% 3.37/1.02  sim_ac_normalised:                      0
% 3.37/1.02  sim_smt_subsumption:                    0
% 3.37/1.02  
%------------------------------------------------------------------------------
