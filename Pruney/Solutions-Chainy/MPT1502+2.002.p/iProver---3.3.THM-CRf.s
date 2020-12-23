%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:08 EST 2020

% Result     : Theorem 31.49s
% Output     : CNFRefutation 31.49s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 737 expanded)
%              Number of clauses        :  137 ( 188 expanded)
%              Number of leaves         :   22 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          : 1179 (4283 expanded)
%              Number of equality atoms :   94 ( 129 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   15 (   5 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
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
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
     => ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,sK5)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,sK4,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,sK4,X2)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(sK3,k3_lattices(sK3,X1,k16_lattice3(sK3,X2)),k16_lattice3(sK3,a_3_4_lattice3(sK3,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f49,f48,f47])).

fof(f77,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f53,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_lattices(X0,X1,X2)
                   => r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X3)
              & k3_lattices(X1,X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( r2_hidden(X5,X3)
              & k3_lattices(X1,X2,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X3)
          & k3_lattices(X1,X2,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK1(X0,X1,X2,X3),X3)
        & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2,X3),X3)
            & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
            & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f42])).

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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK2(X0,X1,X2),X1)
        & r3_lattice3(X0,sK2(X0,X1,X2),X2)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK2(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK2(X0,X1,X2),X2)
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f81,plain,(
    ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
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

cnf(c_483,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_487,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_2,c_1])).

cnf(c_14,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_562,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X3,X4,X5)
    | ~ r2_hidden(X6,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v10_lattices(X3)
    | X0 != X3
    | X1 != X4
    | X6 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_487,c_14])).

cnf(c_563,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_29,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_877,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_563,c_29])).

cnf(c_878,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_882,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_30,c_27])).

cnf(c_883,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_1225,plain,
    ( ~ r3_lattice3(sK3,X0_54,X0_55)
    | r3_lattices(sK3,X0_54,X1_54)
    | ~ r2_hidden(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_883])).

cnf(c_68184,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55)
    | r3_lattices(sK3,k16_lattice3(sK3,X0_55),X0_54)
    | ~ r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_79550,plain,
    ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
    | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | ~ r2_hidden(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_68184])).

cnf(c_3,plain,
    ( v5_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ v5_lattices(X0)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_376,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_3,c_10])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_380,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_10,c_4,c_3,c_2,c_1,c_0])).

cnf(c_381,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_925,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_29])).

cnf(c_926,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_930,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_30,c_27])).

cnf(c_931,plain,
    ( ~ r3_lattices(sK3,X0,X1)
    | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_930])).

cnf(c_1223,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | r3_lattices(sK3,k3_lattices(sK3,X2_54,X0_54),k3_lattices(sK3,X2_54,X1_54))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_931])).

cnf(c_4546,plain,
    ( ~ r3_lattices(sK3,X0_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | r3_lattices(sK3,k3_lattices(sK3,X1_54,X0_54),k3_lattices(sK3,X1_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_35138,plain,
    ( r3_lattices(sK3,k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)),k3_lattices(sK3,X0_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,X0_55),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4546])).

cnf(c_35140,plain,
    ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_35138])).

cnf(c_1242,plain,
    ( ~ r3_lattices(X0_53,X0_54,X1_54)
    | r3_lattices(X0_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_1725,plain,
    ( ~ r3_lattices(sK3,X0_54,X1_54)
    | r3_lattices(sK3,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_6650,plain,
    ( r3_lattices(sK3,X0_54,X1_54)
    | ~ r3_lattices(sK3,k3_lattices(sK3,X2_54,X3_54),k3_lattices(sK3,X2_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | X0_54 != k3_lattices(sK3,X2_54,X3_54)
    | X1_54 != k3_lattices(sK3,X2_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_11032,plain,
    ( r3_lattices(sK3,X0_54,sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,X1_54),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | X0_54 != k3_lattices(sK3,sK4,X1_54)
    | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6650])).

cnf(c_24927,plain,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,X0_54),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
    | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) != k3_lattices(sK3,sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_11032])).

cnf(c_33851,plain,
    ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
    | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) != k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_24927])).

cnf(c_1237,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_3827,plain,
    ( sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1239,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2199,plain,
    ( X0_54 != X1_54
    | sK0(sK3,X2_54,X0_55) != X1_54
    | sK0(sK3,X2_54,X0_55) = X0_54 ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_3187,plain,
    ( X0_54 != sK0(sK3,X1_54,X0_55)
    | sK0(sK3,X1_54,X0_55) = X0_54
    | sK0(sK3,X1_54,X0_55) != sK0(sK3,X1_54,X0_55) ),
    inference(instantiation,[status(thm)],[c_2199])).

cnf(c_3507,plain,
    ( sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3187])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_640,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_641,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_645,plain,
    ( m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_30,c_29,c_27])).

cnf(c_646,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_1233,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(c_1678,plain,
    ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_3425,plain,
    ( ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_9,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_451,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_455,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_9,c_2,c_1,c_0])).

cnf(c_11,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_532,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X3,X4,X5)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v10_lattices(X3)
    | X0 != X3
    | X1 != X4
    | sK0(X0,X1,X2) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_455,c_11])).

cnf(c_533,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_13,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | r3_lattice3(X0,X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_13])).

cnf(c_538,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_904,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_538,c_29])).

cnf(c_905,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_909,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_30,c_27])).

cnf(c_1224,plain,
    ( r3_lattice3(sK3,X0_54,X0_55)
    | ~ r3_lattices(sK3,X0_54,sK0(sK3,X0_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_909])).

cnf(c_2812,plain,
    ( r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_661,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_662,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_30,c_29,c_27])).

cnf(c_667,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_1232,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_54,sK1(X0_54,sK3,X1_54,X0_55)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_1844,plain,
    ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) = sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_2383,plain,
    ( ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | r2_hidden(sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_682,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
    | r2_hidden(sK1(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_683,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_30,c_29,c_27])).

cnf(c_688,plain,
    ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
    | r2_hidden(sK1(X0,sK3,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_687])).

cnf(c_1231,plain,
    ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | r2_hidden(sK1(X0_54,sK3,X1_54,X0_55),X0_55)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_688])).

cnf(c_1845,plain,
    ( r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
    | ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2384,plain,
    ( r2_hidden(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
    | ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_12,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1049,plain,
    ( r3_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_1050,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1050,c_27])).

cnf(c_1055,plain,
    ( r3_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1054])).

cnf(c_1218,plain,
    ( r3_lattice3(sK3,X0_54,X0_55)
    | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1055])).

cnf(c_1679,plain,
    ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
    | r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_2047,plain,
    ( r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_7,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_6])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_346])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_952,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_421,c_29])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k3_lattices(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k3_lattices(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_953,c_30,c_27])).

cnf(c_958,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(k3_lattices(sK3,X1,X0),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_957])).

cnf(c_1222,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(k3_lattices(sK3,X1_54,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_958])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | m1_subset_1(k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_2010,plain,
    ( m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_15,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1013,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_1014,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_1018,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_27])).

cnf(c_23,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_742,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_743,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_747,plain,
    ( ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_30,c_29,c_27])).

cnf(c_748,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_747])).

cnf(c_1076,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1018,c_748])).

cnf(c_1217,plain,
    ( ~ r3_lattice3(sK3,X0_54,X0_55)
    | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1076])).

cnf(c_1968,plain,
    ( ~ r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
    | r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))
    | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_1240,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | k3_lattices(X0_53,X0_54,X2_54) = k3_lattices(X0_53,X1_54,X3_54) ),
    theory(equality)).

cnf(c_1933,plain,
    ( k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) = k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,X0_55)
    | sK4 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_1934,plain,
    ( k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) = k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5))
    | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_1220,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_1018])).

cnf(c_1297,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_24,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_179,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_15])).

cnf(c_727,plain,
    ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_28])).

cnf(c_728,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_30,c_29,c_27])).

cnf(c_1229,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_732])).

cnf(c_1272,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_1238,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1256,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_1255,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1245,plain,
    ( X0_55 != X1_55
    | k16_lattice3(X0_53,X0_55) = k16_lattice3(X0_53,X1_55) ),
    theory(equality)).

cnf(c_1252,plain,
    ( sK5 != sK5
    | k16_lattice3(sK3,sK5) = k16_lattice3(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79550,c_35140,c_33851,c_3827,c_3507,c_3425,c_2812,c_2383,c_2384,c_2047,c_2010,c_1968,c_1934,c_1297,c_1272,c_1256,c_1255,c_1252,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.49/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.49/4.49  
% 31.49/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.49/4.49  
% 31.49/4.49  ------  iProver source info
% 31.49/4.49  
% 31.49/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.49/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.49/4.49  git: non_committed_changes: false
% 31.49/4.49  git: last_make_outside_of_git: false
% 31.49/4.49  
% 31.49/4.49  ------ 
% 31.49/4.49  
% 31.49/4.49  ------ Input Options
% 31.49/4.49  
% 31.49/4.49  --out_options                           all
% 31.49/4.49  --tptp_safe_out                         true
% 31.49/4.49  --problem_path                          ""
% 31.49/4.49  --include_path                          ""
% 31.49/4.49  --clausifier                            res/vclausify_rel
% 31.49/4.49  --clausifier_options                    ""
% 31.49/4.49  --stdin                                 false
% 31.49/4.49  --stats_out                             all
% 31.49/4.49  
% 31.49/4.49  ------ General Options
% 31.49/4.49  
% 31.49/4.49  --fof                                   false
% 31.49/4.49  --time_out_real                         305.
% 31.49/4.49  --time_out_virtual                      -1.
% 31.49/4.49  --symbol_type_check                     false
% 31.49/4.49  --clausify_out                          false
% 31.49/4.49  --sig_cnt_out                           false
% 31.49/4.49  --trig_cnt_out                          false
% 31.49/4.49  --trig_cnt_out_tolerance                1.
% 31.49/4.49  --trig_cnt_out_sk_spl                   false
% 31.49/4.49  --abstr_cl_out                          false
% 31.49/4.49  
% 31.49/4.49  ------ Global Options
% 31.49/4.49  
% 31.49/4.49  --schedule                              default
% 31.49/4.49  --add_important_lit                     false
% 31.49/4.49  --prop_solver_per_cl                    1000
% 31.49/4.49  --min_unsat_core                        false
% 31.49/4.49  --soft_assumptions                      false
% 31.49/4.49  --soft_lemma_size                       3
% 31.49/4.49  --prop_impl_unit_size                   0
% 31.49/4.49  --prop_impl_unit                        []
% 31.49/4.49  --share_sel_clauses                     true
% 31.49/4.49  --reset_solvers                         false
% 31.49/4.49  --bc_imp_inh                            [conj_cone]
% 31.49/4.49  --conj_cone_tolerance                   3.
% 31.49/4.49  --extra_neg_conj                        none
% 31.49/4.49  --large_theory_mode                     true
% 31.49/4.49  --prolific_symb_bound                   200
% 31.49/4.49  --lt_threshold                          2000
% 31.49/4.49  --clause_weak_htbl                      true
% 31.49/4.49  --gc_record_bc_elim                     false
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing Options
% 31.49/4.49  
% 31.49/4.49  --preprocessing_flag                    true
% 31.49/4.49  --time_out_prep_mult                    0.1
% 31.49/4.49  --splitting_mode                        input
% 31.49/4.49  --splitting_grd                         true
% 31.49/4.49  --splitting_cvd                         false
% 31.49/4.49  --splitting_cvd_svl                     false
% 31.49/4.49  --splitting_nvd                         32
% 31.49/4.49  --sub_typing                            true
% 31.49/4.49  --prep_gs_sim                           true
% 31.49/4.49  --prep_unflatten                        true
% 31.49/4.49  --prep_res_sim                          true
% 31.49/4.49  --prep_upred                            true
% 31.49/4.49  --prep_sem_filter                       exhaustive
% 31.49/4.49  --prep_sem_filter_out                   false
% 31.49/4.49  --pred_elim                             true
% 31.49/4.49  --res_sim_input                         true
% 31.49/4.49  --eq_ax_congr_red                       true
% 31.49/4.49  --pure_diseq_elim                       true
% 31.49/4.49  --brand_transform                       false
% 31.49/4.49  --non_eq_to_eq                          false
% 31.49/4.49  --prep_def_merge                        true
% 31.49/4.49  --prep_def_merge_prop_impl              false
% 31.49/4.49  --prep_def_merge_mbd                    true
% 31.49/4.49  --prep_def_merge_tr_red                 false
% 31.49/4.49  --prep_def_merge_tr_cl                  false
% 31.49/4.49  --smt_preprocessing                     true
% 31.49/4.49  --smt_ac_axioms                         fast
% 31.49/4.49  --preprocessed_out                      false
% 31.49/4.49  --preprocessed_stats                    false
% 31.49/4.49  
% 31.49/4.49  ------ Abstraction refinement Options
% 31.49/4.49  
% 31.49/4.49  --abstr_ref                             []
% 31.49/4.49  --abstr_ref_prep                        false
% 31.49/4.49  --abstr_ref_until_sat                   false
% 31.49/4.49  --abstr_ref_sig_restrict                funpre
% 31.49/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.49/4.49  --abstr_ref_under                       []
% 31.49/4.49  
% 31.49/4.49  ------ SAT Options
% 31.49/4.49  
% 31.49/4.49  --sat_mode                              false
% 31.49/4.49  --sat_fm_restart_options                ""
% 31.49/4.49  --sat_gr_def                            false
% 31.49/4.49  --sat_epr_types                         true
% 31.49/4.49  --sat_non_cyclic_types                  false
% 31.49/4.49  --sat_finite_models                     false
% 31.49/4.49  --sat_fm_lemmas                         false
% 31.49/4.49  --sat_fm_prep                           false
% 31.49/4.49  --sat_fm_uc_incr                        true
% 31.49/4.49  --sat_out_model                         small
% 31.49/4.49  --sat_out_clauses                       false
% 31.49/4.49  
% 31.49/4.49  ------ QBF Options
% 31.49/4.49  
% 31.49/4.49  --qbf_mode                              false
% 31.49/4.49  --qbf_elim_univ                         false
% 31.49/4.49  --qbf_dom_inst                          none
% 31.49/4.49  --qbf_dom_pre_inst                      false
% 31.49/4.49  --qbf_sk_in                             false
% 31.49/4.49  --qbf_pred_elim                         true
% 31.49/4.49  --qbf_split                             512
% 31.49/4.49  
% 31.49/4.49  ------ BMC1 Options
% 31.49/4.49  
% 31.49/4.49  --bmc1_incremental                      false
% 31.49/4.49  --bmc1_axioms                           reachable_all
% 31.49/4.49  --bmc1_min_bound                        0
% 31.49/4.49  --bmc1_max_bound                        -1
% 31.49/4.49  --bmc1_max_bound_default                -1
% 31.49/4.49  --bmc1_symbol_reachability              true
% 31.49/4.49  --bmc1_property_lemmas                  false
% 31.49/4.49  --bmc1_k_induction                      false
% 31.49/4.49  --bmc1_non_equiv_states                 false
% 31.49/4.49  --bmc1_deadlock                         false
% 31.49/4.49  --bmc1_ucm                              false
% 31.49/4.49  --bmc1_add_unsat_core                   none
% 31.49/4.49  --bmc1_unsat_core_children              false
% 31.49/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.49/4.49  --bmc1_out_stat                         full
% 31.49/4.49  --bmc1_ground_init                      false
% 31.49/4.49  --bmc1_pre_inst_next_state              false
% 31.49/4.49  --bmc1_pre_inst_state                   false
% 31.49/4.49  --bmc1_pre_inst_reach_state             false
% 31.49/4.49  --bmc1_out_unsat_core                   false
% 31.49/4.49  --bmc1_aig_witness_out                  false
% 31.49/4.49  --bmc1_verbose                          false
% 31.49/4.49  --bmc1_dump_clauses_tptp                false
% 31.49/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.49/4.49  --bmc1_dump_file                        -
% 31.49/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.49/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.49/4.49  --bmc1_ucm_extend_mode                  1
% 31.49/4.49  --bmc1_ucm_init_mode                    2
% 31.49/4.49  --bmc1_ucm_cone_mode                    none
% 31.49/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.49/4.49  --bmc1_ucm_relax_model                  4
% 31.49/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.49/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.49/4.49  --bmc1_ucm_layered_model                none
% 31.49/4.49  --bmc1_ucm_max_lemma_size               10
% 31.49/4.49  
% 31.49/4.49  ------ AIG Options
% 31.49/4.49  
% 31.49/4.49  --aig_mode                              false
% 31.49/4.49  
% 31.49/4.49  ------ Instantiation Options
% 31.49/4.49  
% 31.49/4.49  --instantiation_flag                    true
% 31.49/4.49  --inst_sos_flag                         true
% 31.49/4.49  --inst_sos_phase                        true
% 31.49/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.49/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.49/4.49  --inst_lit_sel_side                     num_symb
% 31.49/4.49  --inst_solver_per_active                1400
% 31.49/4.49  --inst_solver_calls_frac                1.
% 31.49/4.49  --inst_passive_queue_type               priority_queues
% 31.49/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.49/4.49  --inst_passive_queues_freq              [25;2]
% 31.49/4.49  --inst_dismatching                      true
% 31.49/4.49  --inst_eager_unprocessed_to_passive     true
% 31.49/4.49  --inst_prop_sim_given                   true
% 31.49/4.49  --inst_prop_sim_new                     false
% 31.49/4.49  --inst_subs_new                         false
% 31.49/4.49  --inst_eq_res_simp                      false
% 31.49/4.49  --inst_subs_given                       false
% 31.49/4.49  --inst_orphan_elimination               true
% 31.49/4.49  --inst_learning_loop_flag               true
% 31.49/4.49  --inst_learning_start                   3000
% 31.49/4.49  --inst_learning_factor                  2
% 31.49/4.49  --inst_start_prop_sim_after_learn       3
% 31.49/4.49  --inst_sel_renew                        solver
% 31.49/4.49  --inst_lit_activity_flag                true
% 31.49/4.49  --inst_restr_to_given                   false
% 31.49/4.49  --inst_activity_threshold               500
% 31.49/4.49  --inst_out_proof                        true
% 31.49/4.49  
% 31.49/4.49  ------ Resolution Options
% 31.49/4.49  
% 31.49/4.49  --resolution_flag                       true
% 31.49/4.49  --res_lit_sel                           adaptive
% 31.49/4.49  --res_lit_sel_side                      none
% 31.49/4.49  --res_ordering                          kbo
% 31.49/4.49  --res_to_prop_solver                    active
% 31.49/4.49  --res_prop_simpl_new                    false
% 31.49/4.49  --res_prop_simpl_given                  true
% 31.49/4.49  --res_passive_queue_type                priority_queues
% 31.49/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.49/4.49  --res_passive_queues_freq               [15;5]
% 31.49/4.49  --res_forward_subs                      full
% 31.49/4.49  --res_backward_subs                     full
% 31.49/4.49  --res_forward_subs_resolution           true
% 31.49/4.49  --res_backward_subs_resolution          true
% 31.49/4.49  --res_orphan_elimination                true
% 31.49/4.49  --res_time_limit                        2.
% 31.49/4.49  --res_out_proof                         true
% 31.49/4.49  
% 31.49/4.49  ------ Superposition Options
% 31.49/4.49  
% 31.49/4.49  --superposition_flag                    true
% 31.49/4.49  --sup_passive_queue_type                priority_queues
% 31.49/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.49/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.49/4.49  --demod_completeness_check              fast
% 31.49/4.49  --demod_use_ground                      true
% 31.49/4.49  --sup_to_prop_solver                    passive
% 31.49/4.49  --sup_prop_simpl_new                    true
% 31.49/4.49  --sup_prop_simpl_given                  true
% 31.49/4.49  --sup_fun_splitting                     true
% 31.49/4.49  --sup_smt_interval                      50000
% 31.49/4.49  
% 31.49/4.49  ------ Superposition Simplification Setup
% 31.49/4.49  
% 31.49/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.49/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.49/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.49/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.49/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.49/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.49/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.49/4.49  --sup_immed_triv                        [TrivRules]
% 31.49/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_immed_bw_main                     []
% 31.49/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.49/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.49/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_input_bw                          []
% 31.49/4.49  
% 31.49/4.49  ------ Combination Options
% 31.49/4.49  
% 31.49/4.49  --comb_res_mult                         3
% 31.49/4.49  --comb_sup_mult                         2
% 31.49/4.49  --comb_inst_mult                        10
% 31.49/4.49  
% 31.49/4.49  ------ Debug Options
% 31.49/4.49  
% 31.49/4.49  --dbg_backtrace                         false
% 31.49/4.49  --dbg_dump_prop_clauses                 false
% 31.49/4.49  --dbg_dump_prop_clauses_file            -
% 31.49/4.49  --dbg_out_stat                          false
% 31.49/4.49  ------ Parsing...
% 31.49/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.49/4.49  ------ Proving...
% 31.49/4.49  ------ Problem Properties 
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  clauses                                 19
% 31.49/4.49  conjectures                             2
% 31.49/4.49  EPR                                     0
% 31.49/4.49  Horn                                    15
% 31.49/4.49  unary                                   4
% 31.49/4.49  binary                                  0
% 31.49/4.49  lits                                    58
% 31.49/4.49  lits eq                                 4
% 31.49/4.49  fd_pure                                 0
% 31.49/4.49  fd_pseudo                               0
% 31.49/4.49  fd_cond                                 0
% 31.49/4.49  fd_pseudo_cond                          3
% 31.49/4.49  AC symbols                              0
% 31.49/4.49  
% 31.49/4.49  ------ Schedule dynamic 5 is on 
% 31.49/4.49  
% 31.49/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  ------ 
% 31.49/4.49  Current options:
% 31.49/4.49  ------ 
% 31.49/4.49  
% 31.49/4.49  ------ Input Options
% 31.49/4.49  
% 31.49/4.49  --out_options                           all
% 31.49/4.49  --tptp_safe_out                         true
% 31.49/4.49  --problem_path                          ""
% 31.49/4.49  --include_path                          ""
% 31.49/4.49  --clausifier                            res/vclausify_rel
% 31.49/4.49  --clausifier_options                    ""
% 31.49/4.49  --stdin                                 false
% 31.49/4.49  --stats_out                             all
% 31.49/4.49  
% 31.49/4.49  ------ General Options
% 31.49/4.49  
% 31.49/4.49  --fof                                   false
% 31.49/4.49  --time_out_real                         305.
% 31.49/4.49  --time_out_virtual                      -1.
% 31.49/4.49  --symbol_type_check                     false
% 31.49/4.49  --clausify_out                          false
% 31.49/4.49  --sig_cnt_out                           false
% 31.49/4.49  --trig_cnt_out                          false
% 31.49/4.49  --trig_cnt_out_tolerance                1.
% 31.49/4.49  --trig_cnt_out_sk_spl                   false
% 31.49/4.49  --abstr_cl_out                          false
% 31.49/4.49  
% 31.49/4.49  ------ Global Options
% 31.49/4.49  
% 31.49/4.49  --schedule                              default
% 31.49/4.49  --add_important_lit                     false
% 31.49/4.49  --prop_solver_per_cl                    1000
% 31.49/4.49  --min_unsat_core                        false
% 31.49/4.49  --soft_assumptions                      false
% 31.49/4.49  --soft_lemma_size                       3
% 31.49/4.49  --prop_impl_unit_size                   0
% 31.49/4.49  --prop_impl_unit                        []
% 31.49/4.49  --share_sel_clauses                     true
% 31.49/4.49  --reset_solvers                         false
% 31.49/4.49  --bc_imp_inh                            [conj_cone]
% 31.49/4.49  --conj_cone_tolerance                   3.
% 31.49/4.49  --extra_neg_conj                        none
% 31.49/4.49  --large_theory_mode                     true
% 31.49/4.49  --prolific_symb_bound                   200
% 31.49/4.49  --lt_threshold                          2000
% 31.49/4.49  --clause_weak_htbl                      true
% 31.49/4.49  --gc_record_bc_elim                     false
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing Options
% 31.49/4.49  
% 31.49/4.49  --preprocessing_flag                    true
% 31.49/4.49  --time_out_prep_mult                    0.1
% 31.49/4.49  --splitting_mode                        input
% 31.49/4.49  --splitting_grd                         true
% 31.49/4.49  --splitting_cvd                         false
% 31.49/4.49  --splitting_cvd_svl                     false
% 31.49/4.49  --splitting_nvd                         32
% 31.49/4.49  --sub_typing                            true
% 31.49/4.49  --prep_gs_sim                           true
% 31.49/4.49  --prep_unflatten                        true
% 31.49/4.49  --prep_res_sim                          true
% 31.49/4.49  --prep_upred                            true
% 31.49/4.49  --prep_sem_filter                       exhaustive
% 31.49/4.49  --prep_sem_filter_out                   false
% 31.49/4.49  --pred_elim                             true
% 31.49/4.49  --res_sim_input                         true
% 31.49/4.49  --eq_ax_congr_red                       true
% 31.49/4.49  --pure_diseq_elim                       true
% 31.49/4.49  --brand_transform                       false
% 31.49/4.49  --non_eq_to_eq                          false
% 31.49/4.49  --prep_def_merge                        true
% 31.49/4.49  --prep_def_merge_prop_impl              false
% 31.49/4.49  --prep_def_merge_mbd                    true
% 31.49/4.49  --prep_def_merge_tr_red                 false
% 31.49/4.49  --prep_def_merge_tr_cl                  false
% 31.49/4.49  --smt_preprocessing                     true
% 31.49/4.49  --smt_ac_axioms                         fast
% 31.49/4.49  --preprocessed_out                      false
% 31.49/4.49  --preprocessed_stats                    false
% 31.49/4.49  
% 31.49/4.49  ------ Abstraction refinement Options
% 31.49/4.49  
% 31.49/4.49  --abstr_ref                             []
% 31.49/4.49  --abstr_ref_prep                        false
% 31.49/4.49  --abstr_ref_until_sat                   false
% 31.49/4.49  --abstr_ref_sig_restrict                funpre
% 31.49/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.49/4.49  --abstr_ref_under                       []
% 31.49/4.49  
% 31.49/4.49  ------ SAT Options
% 31.49/4.49  
% 31.49/4.49  --sat_mode                              false
% 31.49/4.49  --sat_fm_restart_options                ""
% 31.49/4.49  --sat_gr_def                            false
% 31.49/4.49  --sat_epr_types                         true
% 31.49/4.49  --sat_non_cyclic_types                  false
% 31.49/4.49  --sat_finite_models                     false
% 31.49/4.49  --sat_fm_lemmas                         false
% 31.49/4.49  --sat_fm_prep                           false
% 31.49/4.49  --sat_fm_uc_incr                        true
% 31.49/4.49  --sat_out_model                         small
% 31.49/4.49  --sat_out_clauses                       false
% 31.49/4.49  
% 31.49/4.49  ------ QBF Options
% 31.49/4.49  
% 31.49/4.49  --qbf_mode                              false
% 31.49/4.49  --qbf_elim_univ                         false
% 31.49/4.49  --qbf_dom_inst                          none
% 31.49/4.49  --qbf_dom_pre_inst                      false
% 31.49/4.49  --qbf_sk_in                             false
% 31.49/4.49  --qbf_pred_elim                         true
% 31.49/4.49  --qbf_split                             512
% 31.49/4.49  
% 31.49/4.49  ------ BMC1 Options
% 31.49/4.49  
% 31.49/4.49  --bmc1_incremental                      false
% 31.49/4.49  --bmc1_axioms                           reachable_all
% 31.49/4.49  --bmc1_min_bound                        0
% 31.49/4.49  --bmc1_max_bound                        -1
% 31.49/4.49  --bmc1_max_bound_default                -1
% 31.49/4.49  --bmc1_symbol_reachability              true
% 31.49/4.49  --bmc1_property_lemmas                  false
% 31.49/4.49  --bmc1_k_induction                      false
% 31.49/4.49  --bmc1_non_equiv_states                 false
% 31.49/4.49  --bmc1_deadlock                         false
% 31.49/4.49  --bmc1_ucm                              false
% 31.49/4.49  --bmc1_add_unsat_core                   none
% 31.49/4.49  --bmc1_unsat_core_children              false
% 31.49/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.49/4.49  --bmc1_out_stat                         full
% 31.49/4.49  --bmc1_ground_init                      false
% 31.49/4.49  --bmc1_pre_inst_next_state              false
% 31.49/4.49  --bmc1_pre_inst_state                   false
% 31.49/4.49  --bmc1_pre_inst_reach_state             false
% 31.49/4.49  --bmc1_out_unsat_core                   false
% 31.49/4.49  --bmc1_aig_witness_out                  false
% 31.49/4.49  --bmc1_verbose                          false
% 31.49/4.49  --bmc1_dump_clauses_tptp                false
% 31.49/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.49/4.49  --bmc1_dump_file                        -
% 31.49/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.49/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.49/4.49  --bmc1_ucm_extend_mode                  1
% 31.49/4.49  --bmc1_ucm_init_mode                    2
% 31.49/4.49  --bmc1_ucm_cone_mode                    none
% 31.49/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.49/4.49  --bmc1_ucm_relax_model                  4
% 31.49/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.49/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.49/4.49  --bmc1_ucm_layered_model                none
% 31.49/4.49  --bmc1_ucm_max_lemma_size               10
% 31.49/4.49  
% 31.49/4.49  ------ AIG Options
% 31.49/4.49  
% 31.49/4.49  --aig_mode                              false
% 31.49/4.49  
% 31.49/4.49  ------ Instantiation Options
% 31.49/4.49  
% 31.49/4.49  --instantiation_flag                    true
% 31.49/4.49  --inst_sos_flag                         true
% 31.49/4.49  --inst_sos_phase                        true
% 31.49/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.49/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.49/4.49  --inst_lit_sel_side                     none
% 31.49/4.49  --inst_solver_per_active                1400
% 31.49/4.49  --inst_solver_calls_frac                1.
% 31.49/4.49  --inst_passive_queue_type               priority_queues
% 31.49/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.49/4.49  --inst_passive_queues_freq              [25;2]
% 31.49/4.49  --inst_dismatching                      true
% 31.49/4.49  --inst_eager_unprocessed_to_passive     true
% 31.49/4.49  --inst_prop_sim_given                   true
% 31.49/4.49  --inst_prop_sim_new                     false
% 31.49/4.49  --inst_subs_new                         false
% 31.49/4.49  --inst_eq_res_simp                      false
% 31.49/4.49  --inst_subs_given                       false
% 31.49/4.49  --inst_orphan_elimination               true
% 31.49/4.49  --inst_learning_loop_flag               true
% 31.49/4.49  --inst_learning_start                   3000
% 31.49/4.49  --inst_learning_factor                  2
% 31.49/4.49  --inst_start_prop_sim_after_learn       3
% 31.49/4.49  --inst_sel_renew                        solver
% 31.49/4.49  --inst_lit_activity_flag                true
% 31.49/4.49  --inst_restr_to_given                   false
% 31.49/4.49  --inst_activity_threshold               500
% 31.49/4.49  --inst_out_proof                        true
% 31.49/4.49  
% 31.49/4.49  ------ Resolution Options
% 31.49/4.49  
% 31.49/4.49  --resolution_flag                       false
% 31.49/4.49  --res_lit_sel                           adaptive
% 31.49/4.49  --res_lit_sel_side                      none
% 31.49/4.49  --res_ordering                          kbo
% 31.49/4.49  --res_to_prop_solver                    active
% 31.49/4.49  --res_prop_simpl_new                    false
% 31.49/4.49  --res_prop_simpl_given                  true
% 31.49/4.49  --res_passive_queue_type                priority_queues
% 31.49/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.49/4.49  --res_passive_queues_freq               [15;5]
% 31.49/4.49  --res_forward_subs                      full
% 31.49/4.49  --res_backward_subs                     full
% 31.49/4.49  --res_forward_subs_resolution           true
% 31.49/4.49  --res_backward_subs_resolution          true
% 31.49/4.49  --res_orphan_elimination                true
% 31.49/4.49  --res_time_limit                        2.
% 31.49/4.49  --res_out_proof                         true
% 31.49/4.49  
% 31.49/4.49  ------ Superposition Options
% 31.49/4.49  
% 31.49/4.49  --superposition_flag                    true
% 31.49/4.49  --sup_passive_queue_type                priority_queues
% 31.49/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.49/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.49/4.49  --demod_completeness_check              fast
% 31.49/4.49  --demod_use_ground                      true
% 31.49/4.49  --sup_to_prop_solver                    passive
% 31.49/4.49  --sup_prop_simpl_new                    true
% 31.49/4.49  --sup_prop_simpl_given                  true
% 31.49/4.49  --sup_fun_splitting                     true
% 31.49/4.49  --sup_smt_interval                      50000
% 31.49/4.49  
% 31.49/4.49  ------ Superposition Simplification Setup
% 31.49/4.49  
% 31.49/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.49/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.49/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.49/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.49/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.49/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.49/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.49/4.49  --sup_immed_triv                        [TrivRules]
% 31.49/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_immed_bw_main                     []
% 31.49/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.49/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.49/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.49/4.49  --sup_input_bw                          []
% 31.49/4.49  
% 31.49/4.49  ------ Combination Options
% 31.49/4.49  
% 31.49/4.49  --comb_res_mult                         3
% 31.49/4.49  --comb_sup_mult                         2
% 31.49/4.49  --comb_inst_mult                        10
% 31.49/4.49  
% 31.49/4.49  ------ Debug Options
% 31.49/4.49  
% 31.49/4.49  --dbg_backtrace                         false
% 31.49/4.49  --dbg_dump_prop_clauses                 false
% 31.49/4.49  --dbg_dump_prop_clauses_file            -
% 31.49/4.49  --dbg_out_stat                          false
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  ------ Proving...
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  % SZS status Theorem for theBenchmark.p
% 31.49/4.49  
% 31.49/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.49/4.49  
% 31.49/4.49  fof(f1,axiom,(
% 31.49/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f13,plain,(
% 31.49/4.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 31.49/4.49    inference(pure_predicate_removal,[],[f1])).
% 31.49/4.49  
% 31.49/4.49  fof(f14,plain,(
% 31.49/4.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 31.49/4.49    inference(ennf_transformation,[],[f13])).
% 31.49/4.49  
% 31.49/4.49  fof(f15,plain,(
% 31.49/4.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 31.49/4.49    inference(flattening,[],[f14])).
% 31.49/4.49  
% 31.49/4.49  fof(f56,plain,(
% 31.49/4.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f15])).
% 31.49/4.49  
% 31.49/4.49  fof(f4,axiom,(
% 31.49/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f19,plain,(
% 31.49/4.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f4])).
% 31.49/4.49  
% 31.49/4.49  fof(f20,plain,(
% 31.49/4.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f19])).
% 31.49/4.49  
% 31.49/4.49  fof(f33,plain,(
% 31.49/4.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(nnf_transformation,[],[f20])).
% 31.49/4.49  
% 31.49/4.49  fof(f60,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f33])).
% 31.49/4.49  
% 31.49/4.49  fof(f54,plain,(
% 31.49/4.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f15])).
% 31.49/4.49  
% 31.49/4.49  fof(f55,plain,(
% 31.49/4.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f15])).
% 31.49/4.49  
% 31.49/4.49  fof(f6,axiom,(
% 31.49/4.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f23,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f6])).
% 31.49/4.49  
% 31.49/4.49  fof(f24,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f23])).
% 31.49/4.49  
% 31.49/4.49  fof(f34,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(nnf_transformation,[],[f24])).
% 31.49/4.49  
% 31.49/4.49  fof(f35,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(rectify,[],[f34])).
% 31.49/4.49  
% 31.49/4.49  fof(f36,plain,(
% 31.49/4.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f37,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 31.49/4.49  
% 31.49/4.49  fof(f62,plain,(
% 31.49/4.49    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f37])).
% 31.49/4.49  
% 31.49/4.49  fof(f10,conjecture,(
% 31.49/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f11,negated_conjecture,(
% 31.49/4.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 31.49/4.49    inference(negated_conjecture,[],[f10])).
% 31.49/4.49  
% 31.49/4.49  fof(f31,plain,(
% 31.49/4.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f11])).
% 31.49/4.49  
% 31.49/4.49  fof(f32,plain,(
% 31.49/4.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f31])).
% 31.49/4.49  
% 31.49/4.49  fof(f49,plain,(
% 31.49/4.49    ( ! [X0,X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) => ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,sK5)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,sK5)))) )),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f48,plain,(
% 31.49/4.49    ( ! [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ~r3_lattices(X0,k3_lattices(X0,sK4,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,sK4,X2))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f47,plain,(
% 31.49/4.49    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ~r3_lattices(sK3,k3_lattices(sK3,X1,k16_lattice3(sK3,X2)),k16_lattice3(sK3,a_3_4_lattice3(sK3,X1,X2))) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f50,plain,(
% 31.49/4.49    (~r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 31.49/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f49,f48,f47])).
% 31.49/4.49  
% 31.49/4.49  fof(f77,plain,(
% 31.49/4.49    v10_lattices(sK3)),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  fof(f76,plain,(
% 31.49/4.49    ~v2_struct_0(sK3)),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  fof(f79,plain,(
% 31.49/4.49    l3_lattices(sK3)),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  fof(f53,plain,(
% 31.49/4.49    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f15])).
% 31.49/4.49  
% 31.49/4.49  fof(f5,axiom,(
% 31.49/4.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)))))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f21,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f5])).
% 31.49/4.49  
% 31.49/4.49  fof(f22,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f21])).
% 31.49/4.49  
% 31.49/4.49  fof(f61,plain,(
% 31.49/4.49    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f22])).
% 31.49/4.49  
% 31.49/4.49  fof(f52,plain,(
% 31.49/4.49    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f15])).
% 31.49/4.49  
% 31.49/4.49  fof(f8,axiom,(
% 31.49/4.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f27,plain,(
% 31.49/4.49    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 31.49/4.49    inference(ennf_transformation,[],[f8])).
% 31.49/4.49  
% 31.49/4.49  fof(f28,plain,(
% 31.49/4.49    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.49/4.49    inference(flattening,[],[f27])).
% 31.49/4.49  
% 31.49/4.49  fof(f38,plain,(
% 31.49/4.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.49/4.49    inference(nnf_transformation,[],[f28])).
% 31.49/4.49  
% 31.49/4.49  fof(f39,plain,(
% 31.49/4.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.49/4.49    inference(rectify,[],[f38])).
% 31.49/4.49  
% 31.49/4.49  fof(f40,plain,(
% 31.49/4.49    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(sK1(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f41,plain,(
% 31.49/4.49    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r2_hidden(sK1(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 31.49/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 31.49/4.49  
% 31.49/4.49  fof(f67,plain,(
% 31.49/4.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f41])).
% 31.49/4.49  
% 31.49/4.49  fof(f78,plain,(
% 31.49/4.49    v4_lattice3(sK3)),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  fof(f59,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f33])).
% 31.49/4.49  
% 31.49/4.49  fof(f65,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f37])).
% 31.49/4.49  
% 31.49/4.49  fof(f63,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f37])).
% 31.49/4.49  
% 31.49/4.49  fof(f68,plain,(
% 31.49/4.49    ( ! [X2,X0,X3,X1] : (k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f41])).
% 31.49/4.49  
% 31.49/4.49  fof(f69,plain,(
% 31.49/4.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X1,X2,X3),X3) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f41])).
% 31.49/4.49  
% 31.49/4.49  fof(f64,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f37])).
% 31.49/4.49  
% 31.49/4.49  fof(f3,axiom,(
% 31.49/4.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f12,plain,(
% 31.49/4.49    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 31.49/4.49    inference(pure_predicate_removal,[],[f3])).
% 31.49/4.49  
% 31.49/4.49  fof(f18,plain,(
% 31.49/4.49    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 31.49/4.49    inference(ennf_transformation,[],[f12])).
% 31.49/4.49  
% 31.49/4.49  fof(f58,plain,(
% 31.49/4.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f18])).
% 31.49/4.49  
% 31.49/4.49  fof(f2,axiom,(
% 31.49/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f16,plain,(
% 31.49/4.49    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f2])).
% 31.49/4.49  
% 31.49/4.49  fof(f17,plain,(
% 31.49/4.49    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f16])).
% 31.49/4.49  
% 31.49/4.49  fof(f57,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f17])).
% 31.49/4.49  
% 31.49/4.49  fof(f7,axiom,(
% 31.49/4.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f25,plain,(
% 31.49/4.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f7])).
% 31.49/4.49  
% 31.49/4.49  fof(f26,plain,(
% 31.49/4.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f25])).
% 31.49/4.49  
% 31.49/4.49  fof(f66,plain,(
% 31.49/4.49    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f26])).
% 31.49/4.49  
% 31.49/4.49  fof(f9,axiom,(
% 31.49/4.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 31.49/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.49/4.49  
% 31.49/4.49  fof(f29,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 31.49/4.49    inference(ennf_transformation,[],[f9])).
% 31.49/4.49  
% 31.49/4.49  fof(f30,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f29])).
% 31.49/4.49  
% 31.49/4.49  fof(f42,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(nnf_transformation,[],[f30])).
% 31.49/4.49  
% 31.49/4.49  fof(f43,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(flattening,[],[f42])).
% 31.49/4.49  
% 31.49/4.49  fof(f44,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(rectify,[],[f43])).
% 31.49/4.49  
% 31.49/4.49  fof(f45,plain,(
% 31.49/4.49    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK2(X0,X1,X2),X1) & r3_lattice3(X0,sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 31.49/4.49    introduced(choice_axiom,[])).
% 31.49/4.49  
% 31.49/4.49  fof(f46,plain,(
% 31.49/4.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK2(X0,X1,X2),X1) & r3_lattice3(X0,sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 31.49/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 31.49/4.49  
% 31.49/4.49  fof(f72,plain,(
% 31.49/4.49    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f46])).
% 31.49/4.49  
% 31.49/4.49  fof(f83,plain,(
% 31.49/4.49    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(equality_resolution,[],[f72])).
% 31.49/4.49  
% 31.49/4.49  fof(f71,plain,(
% 31.49/4.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(cnf_transformation,[],[f46])).
% 31.49/4.49  
% 31.49/4.49  fof(f84,plain,(
% 31.49/4.49    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 31.49/4.49    inference(equality_resolution,[],[f71])).
% 31.49/4.49  
% 31.49/4.49  fof(f81,plain,(
% 31.49/4.49    ~r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  fof(f80,plain,(
% 31.49/4.49    m1_subset_1(sK4,u1_struct_0(sK3))),
% 31.49/4.49    inference(cnf_transformation,[],[f50])).
% 31.49/4.49  
% 31.49/4.49  cnf(c_0,plain,
% 31.49/4.49      ( ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0)
% 31.49/4.49      | v9_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_8,plain,
% 31.49/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v9_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_483,plain,
% 31.49/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(resolution,[status(thm)],[c_0,c_8]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2,plain,
% 31.49/4.49      ( v6_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1,plain,
% 31.49/4.49      ( v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_487,plain,
% 31.49/4.49      ( ~ r1_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_483,c_2,c_1]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_14,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r1_lattices(X0,X1,X3)
% 31.49/4.49      | ~ r2_hidden(X3,X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_562,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X3,X4,X5)
% 31.49/4.49      | ~ r2_hidden(X6,X2)
% 31.49/4.49      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 31.49/4.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X6,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X3)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X3)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X3)
% 31.49/4.49      | X0 != X3
% 31.49/4.49      | X1 != X4
% 31.49/4.49      | X6 != X5 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_487,c_14]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_563,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,X3)
% 31.49/4.49      | ~ r2_hidden(X3,X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_562]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_29,negated_conjecture,
% 31.49/4.49      ( v10_lattices(sK3) ),
% 31.49/4.49      inference(cnf_transformation,[],[f77]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_877,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,X3)
% 31.49/4.49      | ~ r2_hidden(X3,X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_563,c_29]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_878,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,X2)
% 31.49/4.49      | ~ r2_hidden(X2,X1)
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_877]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_30,negated_conjecture,
% 31.49/4.49      ( ~ v2_struct_0(sK3) ),
% 31.49/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_27,negated_conjecture,
% 31.49/4.49      ( l3_lattices(sK3) ),
% 31.49/4.49      inference(cnf_transformation,[],[f79]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_882,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,X2)
% 31.49/4.49      | ~ r2_hidden(X2,X1)
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_878,c_30,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_883,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,X2)
% 31.49/4.49      | ~ r2_hidden(X2,X1)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_882]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1225,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0_54,X0_55)
% 31.49/4.49      | r3_lattices(sK3,X0_54,X1_54)
% 31.49/4.49      | ~ r2_hidden(X1_54,X0_55)
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_883]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_68184,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55)
% 31.49/4.49      | r3_lattices(sK3,k16_lattice3(sK3,X0_55),X0_54)
% 31.49/4.49      | ~ r2_hidden(X0_54,X0_55)
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1225]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_79550,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5)
% 31.49/4.49      | r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | ~ r2_hidden(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 31.49/4.49      | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_68184]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_3,plain,
% 31.49/4.49      ( v5_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_10,plain,
% 31.49/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ v4_lattices(X0)
% 31.49/4.49      | ~ v5_lattices(X0)
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v9_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f61]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_376,plain,
% 31.49/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ v4_lattices(X0)
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0)
% 31.49/4.49      | ~ v9_lattices(X0) ),
% 31.49/4.49      inference(resolution,[status(thm)],[c_3,c_10]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_4,plain,
% 31.49/4.49      ( v4_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_380,plain,
% 31.49/4.49      ( ~ v10_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_376,c_10,c_4,c_3,c_2,c_1,c_0]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_381,plain,
% 31.49/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_380]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_925,plain,
% 31.49/4.49      ( ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_381,c_29]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_926,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_925]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_930,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_926,c_30,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_931,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,X2,X0),k3_lattices(sK3,X2,X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_930]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1223,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,X2_54,X0_54),k3_lattices(sK3,X2_54,X1_54))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X2_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_931]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_4546,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,X1_54,X0_54),k3_lattices(sK3,X1_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1223]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_35138,plain,
% 31.49/4.49      ( r3_lattices(sK3,k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)),k3_lattices(sK3,X0_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,X0_55),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_4546]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_35140,plain,
% 31.49/4.49      ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | ~ m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_35138]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1242,plain,
% 31.49/4.49      ( ~ r3_lattices(X0_53,X0_54,X1_54)
% 31.49/4.49      | r3_lattices(X0_53,X2_54,X3_54)
% 31.49/4.49      | X2_54 != X0_54
% 31.49/4.49      | X3_54 != X1_54 ),
% 31.49/4.49      theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1725,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,X0_54,X1_54)
% 31.49/4.49      | r3_lattices(sK3,X2_54,X3_54)
% 31.49/4.49      | X2_54 != X0_54
% 31.49/4.49      | X3_54 != X1_54 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1242]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_6650,plain,
% 31.49/4.49      ( r3_lattices(sK3,X0_54,X1_54)
% 31.49/4.49      | ~ r3_lattices(sK3,k3_lattices(sK3,X2_54,X3_54),k3_lattices(sK3,X2_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | X0_54 != k3_lattices(sK3,X2_54,X3_54)
% 31.49/4.49      | X1_54 != k3_lattices(sK3,X2_54,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1725]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_11032,plain,
% 31.49/4.49      ( r3_lattices(sK3,X0_54,sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
% 31.49/4.49      | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,X1_54),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | X0_54 != k3_lattices(sK3,sK4,X1_54)
% 31.49/4.49      | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_6650]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_24927,plain,
% 31.49/4.49      ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,X0_54),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
% 31.49/4.49      | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) != k3_lattices(sK3,sK4,X0_54) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_11032]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_33851,plain,
% 31.49/4.49      ( r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
% 31.49/4.49      | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)))
% 31.49/4.49      | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) != k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_24927]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1237,plain,( X0_54 = X0_54 ),theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_3827,plain,
% 31.49/4.49      ( sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) = sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1239,plain,
% 31.49/4.49      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 31.49/4.49      theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2199,plain,
% 31.49/4.49      ( X0_54 != X1_54
% 31.49/4.49      | sK0(sK3,X2_54,X0_55) != X1_54
% 31.49/4.49      | sK0(sK3,X2_54,X0_55) = X0_54 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1239]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_3187,plain,
% 31.49/4.49      ( X0_54 != sK0(sK3,X1_54,X0_55)
% 31.49/4.49      | sK0(sK3,X1_54,X0_55) = X0_54
% 31.49/4.49      | sK0(sK3,X1_54,X0_55) != sK0(sK3,X1_54,X0_55) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_2199]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_3507,plain,
% 31.49/4.49      ( sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) != sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) = k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5))
% 31.49/4.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) != sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_3187]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_19,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 31.49/4.49      | ~ v4_lattice3(X1)
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1) ),
% 31.49/4.49      inference(cnf_transformation,[],[f67]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_28,negated_conjecture,
% 31.49/4.49      ( v4_lattice3(sK3) ),
% 31.49/4.49      inference(cnf_transformation,[],[f78]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_640,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1)
% 31.49/4.49      | sK3 != X1 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_641,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3)
% 31.49/4.49      | ~ v10_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_640]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_645,plain,
% 31.49/4.49      ( m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_641,c_30,c_29,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_646,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(sK1(X0,sK3,X1,X2),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_645]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1233,plain,
% 31.49/4.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(sK1(X0_54,sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_646]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1678,plain,
% 31.49/4.49      ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_3425,plain,
% 31.49/4.49      ( ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | m1_subset_1(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1678]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_9,plain,
% 31.49/4.49      ( r1_lattices(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v9_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_451,plain,
% 31.49/4.49      ( r1_lattices(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ v6_lattices(X0)
% 31.49/4.49      | ~ v8_lattices(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(resolution,[status(thm)],[c_0,c_9]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_455,plain,
% 31.49/4.49      ( r1_lattices(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_451,c_9,c_2,c_1,c_0]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_11,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_532,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X3,X4,X5)
% 31.49/4.49      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 31.49/4.49      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X3)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X3)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X3)
% 31.49/4.49      | X0 != X3
% 31.49/4.49      | X1 != X4
% 31.49/4.49      | sK0(X0,X1,X2) != X5 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_455,c_11]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_533,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_532]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_13,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_537,plain,
% 31.49/4.49      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 31.49/4.49      | r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_533,c_13]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_538,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_537]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_904,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | ~ r3_lattices(X0,X1,sK0(X0,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_538,c_29]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_905,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_904]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_909,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | ~ r3_lattices(sK3,X0,sK0(sK3,X0,X1))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_905,c_30,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1224,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0_54,X0_55)
% 31.49/4.49      | ~ r3_lattices(sK3,X0_54,sK0(sK3,X0_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_909]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2812,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)))
% 31.49/4.49      | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1224]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_18,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | ~ v4_lattice3(X1)
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1)
% 31.49/4.49      | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0 ),
% 31.49/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_661,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1)
% 31.49/4.49      | k3_lattices(X1,X2,sK1(X0,X1,X2,X3)) = X0
% 31.49/4.49      | sK3 != X1 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_662,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3)
% 31.49/4.49      | ~ v10_lattices(sK3)
% 31.49/4.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_661]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_666,plain,
% 31.49/4.49      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_662,c_30,c_29,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_667,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | k3_lattices(sK3,X1,sK1(X0,sK3,X1,X2)) = X0 ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_666]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1232,plain,
% 31.49/4.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | k3_lattices(sK3,X1_54,sK1(X0_54,sK3,X1_54,X0_55)) = X0_54 ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_667]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1844,plain,
% 31.49/4.49      ( ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | k3_lattices(sK3,X1_54,sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55)) = sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1232]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2383,plain,
% 31.49/4.49      ( ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 31.49/4.49      | k3_lattices(sK3,sK4,sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5)) = sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1844]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_17,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | r2_hidden(sK1(X0,X1,X2,X3),X3)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | ~ v4_lattice3(X1)
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1) ),
% 31.49/4.49      inference(cnf_transformation,[],[f69]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_682,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
% 31.49/4.49      | r2_hidden(sK1(X0,X1,X2,X3),X3)
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1)
% 31.49/4.49      | sK3 != X1 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_683,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3)
% 31.49/4.49      | ~ v10_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_682]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_687,plain,
% 31.49/4.49      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 31.49/4.49      | ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_683,c_30,c_29,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_688,plain,
% 31.49/4.49      ( ~ r2_hidden(X0,a_3_4_lattice3(sK3,X1,X2))
% 31.49/4.49      | r2_hidden(sK1(X0,sK3,X1,X2),X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_687]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1231,plain,
% 31.49/4.49      ( ~ r2_hidden(X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | r2_hidden(sK1(X0_54,sK3,X1_54,X0_55),X0_55)
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_688]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1845,plain,
% 31.49/4.49      ( r2_hidden(sK1(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),sK3,X1_54,X0_55),X0_55)
% 31.49/4.49      | ~ r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1231]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2384,plain,
% 31.49/4.49      ( r2_hidden(sK1(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),sK3,sK4,sK5),sK5)
% 31.49/4.49      | ~ r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1845]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_12,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1049,plain,
% 31.49/4.49      ( r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1050,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_1049]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1054,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 31.49/4.49      | r3_lattice3(sK3,X0,X1) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_1050,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1055,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r2_hidden(sK0(sK3,X0,X1),X1)
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_1054]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1218,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0_54,X0_55)
% 31.49/4.49      | r2_hidden(sK0(sK3,X0_54,X0_55),X0_55)
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_1055]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1679,plain,
% 31.49/4.49      ( r3_lattice3(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | r2_hidden(sK0(sK3,X0_54,a_3_4_lattice3(sK3,X1_54,X0_55)),a_3_4_lattice3(sK3,X1_54,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1218]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2047,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | r2_hidden(sK0(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1679]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_7,plain,
% 31.49/4.49      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_6,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ l2_lattices(X1)
% 31.49/4.49      | ~ v4_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1) ),
% 31.49/4.49      inference(cnf_transformation,[],[f57]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_345,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ v4_lattices(X1)
% 31.49/4.49      | ~ l3_lattices(X3)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | X1 != X3 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_7,c_6]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_346,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ v4_lattices(X1)
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_345]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_420,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X3)
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X3)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X3)
% 31.49/4.49      | X1 != X3 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_4,c_346]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_421,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | ~ v10_lattices(X1) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_420]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_952,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 31.49/4.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 31.49/4.49      | m1_subset_1(k3_lattices(X1,X2,X0),u1_struct_0(X1))
% 31.49/4.49      | ~ l3_lattices(X1)
% 31.49/4.49      | v2_struct_0(X1)
% 31.49/4.49      | sK3 != X1 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_421,c_29]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_953,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(k3_lattices(sK3,X0,X1),u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_952]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_957,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(k3_lattices(sK3,X0,X1),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_953,c_30,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_958,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(k3_lattices(sK3,X1,X0),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_957]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1222,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(k3_lattices(sK3,X1_54,X0_54),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_958]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2008,plain,
% 31.49/4.49      ( ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 31.49/4.49      | m1_subset_1(k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55)),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1222]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_2010,plain,
% 31.49/4.49      ( m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_2008]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_15,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f66]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1013,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1014,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_1013]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1018,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_1014,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_23,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 31.49/4.49      | ~ v4_lattice3(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_742,plain,
% 31.49/4.49      ( ~ r3_lattice3(X0,X1,X2)
% 31.49/4.49      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 31.49/4.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_743,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3)
% 31.49/4.49      | ~ v10_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_742]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_747,plain,
% 31.49/4.49      ( ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 31.49/4.49      | ~ r3_lattice3(sK3,X0,X1) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_743,c_30,c_29,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_748,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(sK3,X1),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(renaming,[status(thm)],[c_747]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1076,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0,X1)
% 31.49/4.49      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 31.49/4.49      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(backward_subsumption_resolution,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_1018,c_748]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1217,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,X0_54,X0_55)
% 31.49/4.49      | r3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
% 31.49/4.49      | ~ m1_subset_1(X0_54,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_1076]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1968,plain,
% 31.49/4.49      ( ~ r3_lattice3(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),a_3_4_lattice3(sK3,sK4,sK5))
% 31.49/4.49      | r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5)))
% 31.49/4.49      | ~ m1_subset_1(k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1217]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1240,plain,
% 31.49/4.49      ( X0_54 != X1_54
% 31.49/4.49      | X2_54 != X3_54
% 31.49/4.49      | k3_lattices(X0_53,X0_54,X2_54) = k3_lattices(X0_53,X1_54,X3_54) ),
% 31.49/4.49      theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1933,plain,
% 31.49/4.49      ( k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) = k3_lattices(sK3,X0_54,k16_lattice3(sK3,X0_55))
% 31.49/4.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,X0_55)
% 31.49/4.49      | sK4 != X0_54 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1240]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1934,plain,
% 31.49/4.49      ( k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)) = k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5))
% 31.49/4.49      | k16_lattice3(sK3,sK5) != k16_lattice3(sK3,sK5)
% 31.49/4.49      | sK4 != sK4 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1933]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1220,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(sK3,X0_55),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_1018]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1297,plain,
% 31.49/4.49      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1220]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_24,plain,
% 31.49/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.49/4.49      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 31.49/4.49      | ~ v4_lattice3(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(cnf_transformation,[],[f84]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_179,plain,
% 31.49/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.49/4.49      | ~ v4_lattice3(X0)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_24,c_15]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_727,plain,
% 31.49/4.49      ( r3_lattice3(X0,k16_lattice3(X0,X1),X1)
% 31.49/4.49      | ~ l3_lattices(X0)
% 31.49/4.49      | v2_struct_0(X0)
% 31.49/4.49      | ~ v10_lattices(X0)
% 31.49/4.49      | sK3 != X0 ),
% 31.49/4.49      inference(resolution_lifted,[status(thm)],[c_179,c_28]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_728,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0)
% 31.49/4.49      | ~ l3_lattices(sK3)
% 31.49/4.49      | v2_struct_0(sK3)
% 31.49/4.49      | ~ v10_lattices(sK3) ),
% 31.49/4.49      inference(unflattening,[status(thm)],[c_727]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_732,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0),X0) ),
% 31.49/4.49      inference(global_propositional_subsumption,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_728,c_30,c_29,c_27]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1229,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_55),X0_55) ),
% 31.49/4.49      inference(subtyping,[status(esa)],[c_732]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1272,plain,
% 31.49/4.49      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK5) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1229]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1238,plain,( X0_55 = X0_55 ),theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1256,plain,
% 31.49/4.49      ( sK5 = sK5 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1238]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1255,plain,
% 31.49/4.49      ( sK4 = sK4 ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1245,plain,
% 31.49/4.49      ( X0_55 != X1_55
% 31.49/4.49      | k16_lattice3(X0_53,X0_55) = k16_lattice3(X0_53,X1_55) ),
% 31.49/4.49      theory(equality) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_1252,plain,
% 31.49/4.49      ( sK5 != sK5 | k16_lattice3(sK3,sK5) = k16_lattice3(sK3,sK5) ),
% 31.49/4.49      inference(instantiation,[status(thm)],[c_1245]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_25,negated_conjecture,
% 31.49/4.49      ( ~ r3_lattices(sK3,k3_lattices(sK3,sK4,k16_lattice3(sK3,sK5)),k16_lattice3(sK3,a_3_4_lattice3(sK3,sK4,sK5))) ),
% 31.49/4.49      inference(cnf_transformation,[],[f81]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(c_26,negated_conjecture,
% 31.49/4.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 31.49/4.49      inference(cnf_transformation,[],[f80]) ).
% 31.49/4.49  
% 31.49/4.49  cnf(contradiction,plain,
% 31.49/4.49      ( $false ),
% 31.49/4.49      inference(minisat,
% 31.49/4.49                [status(thm)],
% 31.49/4.49                [c_79550,c_35140,c_33851,c_3827,c_3507,c_3425,c_2812,
% 31.49/4.49                 c_2383,c_2384,c_2047,c_2010,c_1968,c_1934,c_1297,c_1272,
% 31.49/4.49                 c_1256,c_1255,c_1252,c_25,c_26]) ).
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.49/4.49  
% 31.49/4.49  ------                               Statistics
% 31.49/4.49  
% 31.49/4.49  ------ General
% 31.49/4.49  
% 31.49/4.49  abstr_ref_over_cycles:                  0
% 31.49/4.49  abstr_ref_under_cycles:                 0
% 31.49/4.49  gc_basic_clause_elim:                   0
% 31.49/4.49  forced_gc_time:                         0
% 31.49/4.49  parsing_time:                           0.017
% 31.49/4.49  unif_index_cands_time:                  0.
% 31.49/4.49  unif_index_add_time:                    0.
% 31.49/4.49  orderings_time:                         0.
% 31.49/4.49  out_proof_time:                         0.019
% 31.49/4.49  total_time:                             3.586
% 31.49/4.49  num_of_symbols:                         57
% 31.49/4.49  num_of_terms:                           122685
% 31.49/4.49  
% 31.49/4.49  ------ Preprocessing
% 31.49/4.49  
% 31.49/4.49  num_of_splits:                          0
% 31.49/4.49  num_of_split_atoms:                     0
% 31.49/4.49  num_of_reused_defs:                     0
% 31.49/4.49  num_eq_ax_congr_red:                    46
% 31.49/4.49  num_of_sem_filtered_clauses:            1
% 31.49/4.49  num_of_subtypes:                        4
% 31.49/4.49  monotx_restored_types:                  0
% 31.49/4.49  sat_num_of_epr_types:                   0
% 31.49/4.49  sat_num_of_non_cyclic_types:            0
% 31.49/4.49  sat_guarded_non_collapsed_types:        1
% 31.49/4.49  num_pure_diseq_elim:                    0
% 31.49/4.49  simp_replaced_by:                       0
% 31.49/4.49  res_preprocessed:                       108
% 31.49/4.49  prep_upred:                             0
% 31.49/4.49  prep_unflattend:                        28
% 31.49/4.49  smt_new_axioms:                         0
% 31.49/4.49  pred_elim_cands:                        4
% 31.49/4.49  pred_elim:                              11
% 31.49/4.49  pred_elim_cl:                           11
% 31.49/4.49  pred_elim_cycles:                       13
% 31.49/4.49  merged_defs:                            0
% 31.49/4.49  merged_defs_ncl:                        0
% 31.49/4.49  bin_hyper_res:                          0
% 31.49/4.49  prep_cycles:                            4
% 31.49/4.49  pred_elim_time:                         0.016
% 31.49/4.49  splitting_time:                         0.
% 31.49/4.49  sem_filter_time:                        0.
% 31.49/4.49  monotx_time:                            0.
% 31.49/4.49  subtype_inf_time:                       0.
% 31.49/4.49  
% 31.49/4.49  ------ Problem properties
% 31.49/4.49  
% 31.49/4.49  clauses:                                19
% 31.49/4.49  conjectures:                            2
% 31.49/4.49  epr:                                    0
% 31.49/4.49  horn:                                   15
% 31.49/4.49  ground:                                 2
% 31.49/4.49  unary:                                  4
% 31.49/4.49  binary:                                 0
% 31.49/4.49  lits:                                   58
% 31.49/4.49  lits_eq:                                4
% 31.49/4.49  fd_pure:                                0
% 31.49/4.49  fd_pseudo:                              0
% 31.49/4.49  fd_cond:                                0
% 31.49/4.49  fd_pseudo_cond:                         3
% 31.49/4.49  ac_symbols:                             0
% 31.49/4.49  
% 31.49/4.49  ------ Propositional Solver
% 31.49/4.49  
% 31.49/4.49  prop_solver_calls:                      47
% 31.49/4.49  prop_fast_solver_calls:                 3525
% 31.49/4.49  smt_solver_calls:                       0
% 31.49/4.49  smt_fast_solver_calls:                  0
% 31.49/4.49  prop_num_of_clauses:                    31473
% 31.49/4.49  prop_preprocess_simplified:             76667
% 31.49/4.49  prop_fo_subsumed:                       75
% 31.49/4.49  prop_solver_time:                       0.
% 31.49/4.49  smt_solver_time:                        0.
% 31.49/4.49  smt_fast_solver_time:                   0.
% 31.49/4.49  prop_fast_solver_time:                  0.
% 31.49/4.49  prop_unsat_core_time:                   0.002
% 31.49/4.49  
% 31.49/4.49  ------ QBF
% 31.49/4.49  
% 31.49/4.49  qbf_q_res:                              0
% 31.49/4.49  qbf_num_tautologies:                    0
% 31.49/4.49  qbf_prep_cycles:                        0
% 31.49/4.49  
% 31.49/4.49  ------ BMC1
% 31.49/4.49  
% 31.49/4.49  bmc1_current_bound:                     -1
% 31.49/4.49  bmc1_last_solved_bound:                 -1
% 31.49/4.49  bmc1_unsat_core_size:                   -1
% 31.49/4.49  bmc1_unsat_core_parents_size:           -1
% 31.49/4.49  bmc1_merge_next_fun:                    0
% 31.49/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.49/4.49  
% 31.49/4.49  ------ Instantiation
% 31.49/4.49  
% 31.49/4.49  inst_num_of_clauses:                    1384
% 31.49/4.49  inst_num_in_passive:                    762
% 31.49/4.49  inst_num_in_active:                     3054
% 31.49/4.49  inst_num_in_unprocessed:                0
% 31.49/4.49  inst_num_of_loops:                      3630
% 31.49/4.49  inst_num_of_learning_restarts:          1
% 31.49/4.49  inst_num_moves_active_passive:          566
% 31.49/4.49  inst_lit_activity:                      0
% 31.49/4.49  inst_lit_activity_moves:                2
% 31.49/4.49  inst_num_tautologies:                   0
% 31.49/4.49  inst_num_prop_implied:                  0
% 31.49/4.49  inst_num_existing_simplified:           0
% 31.49/4.49  inst_num_eq_res_simplified:             0
% 31.49/4.49  inst_num_child_elim:                    0
% 31.49/4.49  inst_num_of_dismatching_blockings:      14893
% 31.49/4.49  inst_num_of_non_proper_insts:           11293
% 31.49/4.49  inst_num_of_duplicates:                 0
% 31.49/4.49  inst_inst_num_from_inst_to_res:         0
% 31.49/4.49  inst_dismatching_checking_time:         0.
% 31.49/4.49  
% 31.49/4.49  ------ Resolution
% 31.49/4.49  
% 31.49/4.49  res_num_of_clauses:                     29
% 31.49/4.49  res_num_in_passive:                     29
% 31.49/4.49  res_num_in_active:                      0
% 31.49/4.49  res_num_of_loops:                       112
% 31.49/4.49  res_forward_subset_subsumed:            318
% 31.49/4.49  res_backward_subset_subsumed:           0
% 31.49/4.49  res_forward_subsumed:                   0
% 31.49/4.49  res_backward_subsumed:                  0
% 31.49/4.49  res_forward_subsumption_resolution:     1
% 31.49/4.49  res_backward_subsumption_resolution:    1
% 31.49/4.49  res_clause_to_clause_subsumption:       11267
% 31.49/4.49  res_orphan_elimination:                 0
% 31.49/4.49  res_tautology_del:                      881
% 31.49/4.49  res_num_eq_res_simplified:              0
% 31.49/4.49  res_num_sel_changes:                    0
% 31.49/4.49  res_moves_from_active_to_pass:          0
% 31.49/4.49  
% 31.49/4.49  ------ Superposition
% 31.49/4.49  
% 31.49/4.49  sup_time_total:                         0.
% 31.49/4.49  sup_time_generating:                    0.
% 31.49/4.49  sup_time_sim_full:                      0.
% 31.49/4.49  sup_time_sim_immed:                     0.
% 31.49/4.49  
% 31.49/4.49  sup_num_of_clauses:                     1978
% 31.49/4.49  sup_num_in_active:                      723
% 31.49/4.49  sup_num_in_passive:                     1255
% 31.49/4.49  sup_num_of_loops:                       726
% 31.49/4.49  sup_fw_superposition:                   1957
% 31.49/4.49  sup_bw_superposition:                   47
% 31.49/4.49  sup_immediate_simplified:               33
% 31.49/4.49  sup_given_eliminated:                   1
% 31.49/4.49  comparisons_done:                       0
% 31.49/4.49  comparisons_avoided:                    92
% 31.49/4.49  
% 31.49/4.49  ------ Simplifications
% 31.49/4.49  
% 31.49/4.49  
% 31.49/4.49  sim_fw_subset_subsumed:                 14
% 31.49/4.49  sim_bw_subset_subsumed:                 4
% 31.49/4.49  sim_fw_subsumed:                        1
% 31.49/4.49  sim_bw_subsumed:                        1
% 31.49/4.49  sim_fw_subsumption_res:                 0
% 31.49/4.49  sim_bw_subsumption_res:                 0
% 31.49/4.49  sim_tautology_del:                      3
% 31.49/4.49  sim_eq_tautology_del:                   23
% 31.49/4.49  sim_eq_res_simp:                        0
% 31.49/4.49  sim_fw_demodulated:                     2
% 31.49/4.49  sim_bw_demodulated:                     0
% 31.49/4.49  sim_light_normalised:                   18
% 31.49/4.49  sim_joinable_taut:                      0
% 31.49/4.49  sim_joinable_simp:                      0
% 31.49/4.49  sim_ac_normalised:                      0
% 31.49/4.49  sim_smt_subsumption:                    0
% 31.49/4.49  
%------------------------------------------------------------------------------
