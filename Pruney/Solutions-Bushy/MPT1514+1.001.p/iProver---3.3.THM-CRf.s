%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1514+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:46 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 653 expanded)
%              Number of clauses        :  104 ( 161 expanded)
%              Number of leaves         :   14 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  966 (5140 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
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
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,X1,X3)
      | ~ r1_lattices(X0,X2,X3)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r2_hidden(sK5(X3),X2)
        & r3_lattices(X0,X3,sK5(X3))
        & m1_subset_1(sK5(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
     => ( ~ r3_lattices(X0,k15_lattice3(X0,sK3),k15_lattice3(X0,sK4))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,sK4)
                & r3_lattices(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,sK3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
          ( ~ r3_lattices(sK2,k15_lattice3(sK2,X1),k15_lattice3(sK2,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK2,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK2)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )
      & l3_lattices(sK2)
      & v4_lattice3(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r3_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4))
    & ! [X3] :
        ( ( r2_hidden(sK5(X3),sK4)
          & r3_lattices(sK2,X3,sK5(X3))
          & m1_subset_1(sK5(X3),u1_struct_0(sK2)) )
        | ~ r2_hidden(X3,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & l3_lattices(sK2)
    & v4_lattice3(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f43,f42,f41])).

fof(f67,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    v4_lattice3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f49,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f47,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X3] :
      ( r3_lattices(sK2,X3,sK5(X3))
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(X3),u1_struct_0(sK2))
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK4)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f2])).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK1(X0,X1,X2))
        & r4_lattice3(X0,sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f73,plain,(
    ~ r3_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4)) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( v5_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X3)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v5_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X3)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_18])).

cnf(c_367,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X3)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_3,c_327])).

cnf(c_27,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_714,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X3)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_27])).

cnf(c_715,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X1,X2)
    | r1_lattices(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_717,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X1,X2)
    | r1_lattices(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_28,c_25])).

cnf(c_718,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X2,X0)
    | r1_lattices(sK2,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_1173,plain,
    ( ~ r1_lattices(sK2,X0_52,X1_52)
    | ~ r1_lattices(sK2,X2_52,X0_52)
    | r1_lattices(sK2,X2_52,X1_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_718])).

cnf(c_1798,plain,
    ( ~ r1_lattices(sK2,X0_52,X1_52)
    | ~ r1_lattices(sK2,X1_52,k15_lattice3(sK2,X0_53))
    | r1_lattices(sK2,X0_52,k15_lattice3(sK2,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_1981,plain,
    ( ~ r1_lattices(sK2,X0_52,k15_lattice3(sK2,X0_53))
    | ~ r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),X0_52)
    | r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),k15_lattice3(sK2,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_2231,plain,
    ( ~ r1_lattices(sK2,X0_52,k15_lattice3(sK2,sK4))
    | ~ r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),X0_52)
    | r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),k15_lattice3(sK2,sK4))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_3004,plain,
    ( r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),k15_lattice3(sK2,sK4))
    | ~ r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)))
    | ~ r1_lattices(sK2,sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),k15_lattice3(sK2,sK4))
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_20,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( v4_lattice3(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_523,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_524,plain,
    ( r3_lattices(sK2,X0,k15_lattice3(sK2,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,X1)
    | r3_lattices(sK2,X0,k15_lattice3(sK2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_28,c_27,c_25])).

cnf(c_529,plain,
    ( r3_lattices(sK2,X0,k15_lattice3(sK2,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_407,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_17])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_411,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_2,c_1])).

cnf(c_690,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_27])).

cnf(c_691,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_28,c_25])).

cnf(c_696,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_963,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | X0 != X2
    | k15_lattice3(sK2,X3) != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_696])).

cnf(c_964,plain,
    ( r1_lattices(sK2,X0,k15_lattice3(sK2,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_14,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_757,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_758,plain,
    ( m1_subset_1(k15_lattice3(sK2,X0),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( m1_subset_1(k15_lattice3(sK2,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_25])).

cnf(c_976,plain,
    ( r1_lattices(sK2,X0,k15_lattice3(sK2,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_964,c_762])).

cnf(c_1162,plain,
    ( r1_lattices(sK2,X0_52,k15_lattice3(sK2,X0_53))
    | ~ r2_hidden(X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_2105,plain,
    ( r1_lattices(sK2,sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),k15_lattice3(sK2,X0_53))
    | ~ r2_hidden(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),X0_53)
    | ~ m1_subset_1(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_2405,plain,
    ( r1_lattices(sK2,sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),k15_lattice3(sK2,sK4))
    | ~ r2_hidden(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),sK4)
    | ~ m1_subset_1(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_23,negated_conjecture,
    ( r3_lattices(sK2,X0,sK5(X0))
    | ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_942,plain,
    ( r1_lattices(sK2,X0,X1)
    | ~ r2_hidden(X2,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | X0 != X2
    | sK5(X2) != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_696])).

cnf(c_943,plain,
    ( r1_lattices(sK2,X0,sK5(X0))
    | ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_lattices(sK2,X0,sK5(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_24])).

cnf(c_948,plain,
    ( r1_lattices(sK2,X0,sK5(X0))
    | ~ r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_947])).

cnf(c_1163,plain,
    ( r1_lattices(sK2,X0_52,sK5(X0_52))
    | ~ r2_hidden(X0_52,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_948])).

cnf(c_1964,plain,
    ( r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)))
    | ~ r2_hidden(sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK3)
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1180,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK3)
    | r2_hidden(sK5(X0_52),sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1965,plain,
    ( ~ r2_hidden(sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK3)
    | r2_hidden(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),sK4)
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_1179,negated_conjecture,
    ( ~ r2_hidden(X0_52,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1966,plain,
    ( ~ r2_hidden(sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK3)
    | ~ m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK5(sK0(sK2,k15_lattice3(sK2,sK4),sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_6,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_820,plain,
    ( r4_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_821,plain,
    ( r4_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X1)
    | r4_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_25])).

cnf(c_826,plain,
    ( r4_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_825])).

cnf(c_1169,plain,
    ( r4_lattice3(sK2,X0_52,X0_53)
    | r2_hidden(sK0(sK2,X0_52,X0_53),X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_826])).

cnf(c_1763,plain,
    ( r4_lattice3(sK2,k15_lattice3(sK2,X0_53),X1_53)
    | r2_hidden(sK0(sK2,k15_lattice3(sK2,X0_53),X1_53),X1_53)
    | ~ m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_1912,plain,
    ( r4_lattice3(sK2,k15_lattice3(sK2,sK4),sK3)
    | r2_hidden(sK0(sK2,k15_lattice3(sK2,sK4),sK3),sK3)
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_5,plain,
    ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_841,plain,
    ( ~ r1_lattices(X0,sK0(X0,X1,X2),X1)
    | r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_842,plain,
    ( ~ r1_lattices(sK2,sK0(sK2,X0,X1),X0)
    | r4_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_846,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r4_lattice3(sK2,X0,X1)
    | ~ r1_lattices(sK2,sK0(sK2,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_25])).

cnf(c_847,plain,
    ( ~ r1_lattices(sK2,sK0(sK2,X0,X1),X0)
    | r4_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_846])).

cnf(c_1168,plain,
    ( ~ r1_lattices(sK2,sK0(sK2,X0_52,X0_53),X0_52)
    | r4_lattice3(sK2,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_847])).

cnf(c_1760,plain,
    ( ~ r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,X0_53),X1_53),k15_lattice3(sK2,X0_53))
    | r4_lattice3(sK2,k15_lattice3(sK2,X0_53),X1_53)
    | ~ m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1913,plain,
    ( ~ r1_lattices(sK2,sK0(sK2,k15_lattice3(sK2,sK4),sK3),k15_lattice3(sK2,sK4))
    | r4_lattice3(sK2,k15_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_7,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_799,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_800,plain,
    ( r4_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2))
    | ~ l3_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_804,plain,
    ( m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r4_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_25])).

cnf(c_805,plain,
    ( r4_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_804])).

cnf(c_1170,plain,
    ( r4_lattice3(sK2,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_52,X0_53),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_805])).

cnf(c_1752,plain,
    ( r4_lattice3(sK2,k15_lattice3(sK2,X0_53),X1_53)
    | m1_subset_1(sK0(sK2,k15_lattice3(sK2,X0_53),X1_53),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1914,plain,
    ( r4_lattice3(sK2,k15_lattice3(sK2,sK4),sK3)
    | m1_subset_1(sK0(sK2,k15_lattice3(sK2,sK4),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1172,plain,
    ( m1_subset_1(k15_lattice3(sK2,X0_53),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_762])).

cnf(c_1895,plain,
    ( m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_12,plain,
    ( r1_lattices(X0,k15_lattice3(X0,X1),X2)
    | ~ r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r4_lattice3(X0,X2,X1)
    | r1_lattices(X0,k15_lattice3(X0,X1),X2)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_184,plain,
    ( r1_lattices(X0,k15_lattice3(X0,X1),X2)
    | ~ r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_487,plain,
    ( r1_lattices(X0,k15_lattice3(X0,X1),X2)
    | ~ r4_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_26])).

cnf(c_488,plain,
    ( r1_lattices(sK2,k15_lattice3(sK2,X0),X1)
    | ~ r4_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r4_lattice3(sK2,X1,X0)
    | r1_lattices(sK2,k15_lattice3(sK2,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_28,c_27,c_25])).

cnf(c_493,plain,
    ( r1_lattices(sK2,k15_lattice3(sK2,X0),X1)
    | ~ r4_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_1178,plain,
    ( r1_lattices(sK2,k15_lattice3(sK2,X0_53),X0_52)
    | ~ r4_lattice3(sK2,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_493])).

cnf(c_1755,plain,
    ( r1_lattices(sK2,k15_lattice3(sK2,X0_53),k15_lattice3(sK2,X1_53))
    | ~ r4_lattice3(sK2,k15_lattice3(sK2,X1_53),X0_53)
    | ~ m1_subset_1(k15_lattice3(sK2,X1_53),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_1842,plain,
    ( r1_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4))
    | ~ r4_lattice3(sK2,k15_lattice3(sK2,sK4),sK3)
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_21,negated_conjecture,
    ( ~ r3_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_439,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_16])).

cnf(c_443,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_2,c_1])).

cnf(c_666,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_443,c_27])).

cnf(c_667,plain,
    ( r3_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_671,plain,
    ( r3_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_28,c_25])).

cnf(c_672,plain,
    ( r3_lattices(sK2,X0,X1)
    | ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_671])).

cnf(c_930,plain,
    ( ~ r1_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k15_lattice3(sK2,sK4) != X1
    | k15_lattice3(sK2,sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_672])).

cnf(c_931,plain,
    ( ~ r1_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4))
    | ~ m1_subset_1(k15_lattice3(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k15_lattice3(sK2,sK3),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_939,plain,
    ( ~ r1_lattices(sK2,k15_lattice3(sK2,sK3),k15_lattice3(sK2,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_931,c_762,c_762])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3004,c_2405,c_1964,c_1965,c_1966,c_1912,c_1913,c_1914,c_1895,c_1842,c_939])).


%------------------------------------------------------------------------------
