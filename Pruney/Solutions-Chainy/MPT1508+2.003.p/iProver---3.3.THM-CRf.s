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
% DateTime   : Thu Dec  3 12:19:13 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 574 expanded)
%              Number of clauses        :   90 ( 140 expanded)
%              Number of leaves         :   17 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          :  686 (3797 expanded)
%              Number of equality atoms :  102 ( 505 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
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
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK3) != X1
        & r3_lattice3(X0,X1,sK3)
        & r2_hidden(X1,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK2
            & r3_lattice3(X0,sK2,X2)
            & r2_hidden(sK2,X2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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
              ( k16_lattice3(sK1,X2) != X1
              & r3_lattice3(sK1,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v4_lattice3(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k16_lattice3(sK1,sK3) != sK2
    & r3_lattice3(sK1,sK2,sK3)
    & r2_hidden(sK2,sK3)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v4_lattice3(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f38,f37,f36])).

fof(f58,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    k16_lattice3(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK0(X0,X1,X2),X2)
        & sK0(X0,X1,X2) = X0
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK0(X0,X1,X2),X2)
            & sK0(X0,X1,X2) = X0
            & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_259,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_5,c_8])).

cnf(c_297,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_3,c_259])).

cnf(c_23,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_427,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_23])).

cnf(c_428,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_432,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_24,c_21])).

cnf(c_779,plain,
    ( ~ r1_lattices(sK1,X0_51,X1_51)
    | ~ r1_lattices(sK1,X1_51,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_432])).

cnf(c_1417,plain,
    ( ~ r1_lattices(sK1,X0_51,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)))
    | ~ r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1))
    | X0_51 = k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_1419,plain,
    ( ~ r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),sK2)
    | ~ r1_lattices(sK1,sK2,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)))
    | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK2 = k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_786,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1080,plain,
    ( k16_lattice3(sK1,sK3) != X0_51
    | k16_lattice3(sK1,sK3) = sK2
    | sK2 != X0_51 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1315,plain,
    ( k16_lattice3(sK1,sK3) != k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52))
    | k16_lattice3(sK1,sK3) = sK2
    | sK2 != k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1316,plain,
    ( k16_lattice3(sK1,sK3) != k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3))
    | k16_lattice3(sK1,sK3) = sK2
    | sK2 != k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1100,plain,
    ( X0_51 != X1_51
    | k16_lattice3(sK1,sK3) != X1_51
    | k16_lattice3(sK1,sK3) = X0_51 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1171,plain,
    ( X0_51 != k16_lattice3(sK1,sK3)
    | k16_lattice3(sK1,sK3) = X0_51
    | k16_lattice3(sK1,sK3) != k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_1283,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3)
    | k16_lattice3(sK1,sK3) = k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3))
    | k16_lattice3(sK1,sK3) != k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_16,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_377,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_378,plain,
    ( r3_lattices(sK1,X0,k15_lattice3(sK1,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,X1)
    | r3_lattices(sK1,X0,k15_lattice3(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_24,c_23,c_21])).

cnf(c_383,plain,
    ( r3_lattices(sK1,X0,k15_lattice3(sK1,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_7,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_476,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_477,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | v9_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_79,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | v9_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_479,plain,
    ( v9_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_24,c_23,c_21,c_79])).

cnf(c_499,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_479])).

cnf(c_500,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v6_lattices(sK1)
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_73,plain,
    ( v6_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_76,plain,
    ( v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_504,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_24,c_23,c_21,c_73,c_76])).

cnf(c_505,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_504])).

cnf(c_650,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X0 != X2
    | k15_lattice3(sK1,X3) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_505])).

cnf(c_651,plain,
    ( r1_lattices(sK1,X0,k15_lattice3(sK1,X1))
    | ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k15_lattice3(sK1,X1),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_773,plain,
    ( r1_lattices(sK1,X0_51,k15_lattice3(sK1,X0_52))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(k15_lattice3(sK1,X0_52),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_1257,plain,
    ( r1_lattices(sK1,X0_51,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)))
    | ~ r2_hidden(X0_51,a_2_1_lattice3(sK1,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1259,plain,
    ( r1_lattices(sK1,sK2,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)))
    | ~ r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
    | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0_51,X0_53)
    | m1_subset_1(X1_51,X0_53)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1087,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1))
    | X0_51 != k16_lattice3(sK1,X0_52) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1112,plain,
    ( m1_subset_1(k15_lattice3(sK1,X0_52),u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X1_52),u1_struct_0(sK1))
    | k15_lattice3(sK1,X0_52) != k16_lattice3(sK1,X1_52) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_1221,plain,
    ( m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1))
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) != k16_lattice3(sK1,X0_52) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_1223,plain,
    ( m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_787,plain,
    ( ~ r1_lattices(X0_50,X0_51,X1_51)
    | r1_lattices(X0_50,X2_51,X3_51)
    | X2_51 != X0_51
    | X3_51 != X1_51 ),
    theory(equality)).

cnf(c_1090,plain,
    ( r1_lattices(sK1,X0_51,X1_51)
    | ~ r1_lattices(sK1,k16_lattice3(sK1,X0_52),X2_51)
    | X1_51 != X2_51
    | X0_51 != k16_lattice3(sK1,X0_52) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1134,plain,
    ( r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),X0_51)
    | ~ r1_lattices(sK1,k16_lattice3(sK1,X0_52),X1_51)
    | X0_51 != X1_51
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) != k16_lattice3(sK1,X0_52) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1136,plain,
    ( r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),sK2)
    | ~ r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_785,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1099,plain,
    ( k16_lattice3(sK1,sK3) = k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_15,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_399,plain,
    ( r3_lattices(sK1,k16_lattice3(sK1,X0),X1)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,X0)
    | r3_lattices(sK1,k16_lattice3(sK1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_24,c_23,c_21])).

cnf(c_404,plain,
    ( r3_lattices(sK1,k16_lattice3(sK1,X0),X1)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_668,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 != X2
    | k16_lattice3(sK1,X3) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_404,c_505])).

cnf(c_669,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,X0),X1)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_10,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_557,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_558,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1))
    | ~ l3_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X1,X0)
    | r1_lattices(sK1,k16_lattice3(sK1,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_21,c_558])).

cnf(c_674,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,X0),X1)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_673])).

cnf(c_772,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,X0_52),X0_51)
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_674])).

cnf(c_816,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_9,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_572,plain,
    ( ~ l3_lattices(X0)
    | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_573,plain,
    ( ~ l3_lattices(sK1)
    | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_21])).

cnf(c_777,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) = k16_lattice3(sK1,X0_52) ),
    inference(subtyping,[status(esa)],[c_577])).

cnf(c_802,plain,
    ( k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) = k16_lattice3(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_562,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_21])).

cnf(c_778,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_562])).

cnf(c_800,plain,
    ( m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_17,negated_conjecture,
    ( k16_lattice3(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_783,negated_conjecture,
    ( k16_lattice3(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_794,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_11,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r2_hidden(X1,a_2_1_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,negated_conjecture,
    ( r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_359,plain,
    ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK2 != X0
    | sK3 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_360,plain,
    ( r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1419,c_1316,c_1283,c_1259,c_1223,c_1136,c_1099,c_816,c_802,c_800,c_783,c_794,c_360,c_19,c_20,c_21,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.17/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.17/1.00  
% 1.17/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/1.00  
% 1.17/1.00  ------  iProver source info
% 1.17/1.00  
% 1.17/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.17/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/1.00  git: non_committed_changes: false
% 1.17/1.00  git: last_make_outside_of_git: false
% 1.17/1.00  
% 1.17/1.00  ------ 
% 1.17/1.00  
% 1.17/1.00  ------ Input Options
% 1.17/1.00  
% 1.17/1.00  --out_options                           all
% 1.17/1.00  --tptp_safe_out                         true
% 1.17/1.00  --problem_path                          ""
% 1.17/1.00  --include_path                          ""
% 1.17/1.00  --clausifier                            res/vclausify_rel
% 1.17/1.00  --clausifier_options                    --mode clausify
% 1.17/1.00  --stdin                                 false
% 1.17/1.00  --stats_out                             all
% 1.17/1.00  
% 1.17/1.00  ------ General Options
% 1.17/1.00  
% 1.17/1.00  --fof                                   false
% 1.17/1.00  --time_out_real                         305.
% 1.17/1.00  --time_out_virtual                      -1.
% 1.17/1.00  --symbol_type_check                     false
% 1.17/1.00  --clausify_out                          false
% 1.17/1.00  --sig_cnt_out                           false
% 1.17/1.00  --trig_cnt_out                          false
% 1.17/1.00  --trig_cnt_out_tolerance                1.
% 1.17/1.00  --trig_cnt_out_sk_spl                   false
% 1.17/1.00  --abstr_cl_out                          false
% 1.17/1.00  
% 1.17/1.00  ------ Global Options
% 1.17/1.00  
% 1.17/1.00  --schedule                              default
% 1.17/1.00  --add_important_lit                     false
% 1.17/1.00  --prop_solver_per_cl                    1000
% 1.17/1.00  --min_unsat_core                        false
% 1.17/1.00  --soft_assumptions                      false
% 1.17/1.00  --soft_lemma_size                       3
% 1.17/1.00  --prop_impl_unit_size                   0
% 1.17/1.00  --prop_impl_unit                        []
% 1.17/1.00  --share_sel_clauses                     true
% 1.17/1.00  --reset_solvers                         false
% 1.17/1.00  --bc_imp_inh                            [conj_cone]
% 1.17/1.00  --conj_cone_tolerance                   3.
% 1.17/1.00  --extra_neg_conj                        none
% 1.17/1.00  --large_theory_mode                     true
% 1.17/1.00  --prolific_symb_bound                   200
% 1.17/1.00  --lt_threshold                          2000
% 1.17/1.00  --clause_weak_htbl                      true
% 1.17/1.00  --gc_record_bc_elim                     false
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing Options
% 1.17/1.00  
% 1.17/1.00  --preprocessing_flag                    true
% 1.17/1.00  --time_out_prep_mult                    0.1
% 1.17/1.00  --splitting_mode                        input
% 1.17/1.00  --splitting_grd                         true
% 1.17/1.00  --splitting_cvd                         false
% 1.17/1.00  --splitting_cvd_svl                     false
% 1.17/1.00  --splitting_nvd                         32
% 1.17/1.00  --sub_typing                            true
% 1.17/1.00  --prep_gs_sim                           true
% 1.17/1.00  --prep_unflatten                        true
% 1.17/1.00  --prep_res_sim                          true
% 1.17/1.00  --prep_upred                            true
% 1.17/1.00  --prep_sem_filter                       exhaustive
% 1.17/1.00  --prep_sem_filter_out                   false
% 1.17/1.00  --pred_elim                             true
% 1.17/1.00  --res_sim_input                         true
% 1.17/1.00  --eq_ax_congr_red                       true
% 1.17/1.00  --pure_diseq_elim                       true
% 1.17/1.00  --brand_transform                       false
% 1.17/1.00  --non_eq_to_eq                          false
% 1.17/1.00  --prep_def_merge                        true
% 1.17/1.00  --prep_def_merge_prop_impl              false
% 1.17/1.00  --prep_def_merge_mbd                    true
% 1.17/1.00  --prep_def_merge_tr_red                 false
% 1.17/1.00  --prep_def_merge_tr_cl                  false
% 1.17/1.00  --smt_preprocessing                     true
% 1.17/1.00  --smt_ac_axioms                         fast
% 1.17/1.00  --preprocessed_out                      false
% 1.17/1.00  --preprocessed_stats                    false
% 1.17/1.00  
% 1.17/1.00  ------ Abstraction refinement Options
% 1.17/1.00  
% 1.17/1.00  --abstr_ref                             []
% 1.17/1.00  --abstr_ref_prep                        false
% 1.17/1.00  --abstr_ref_until_sat                   false
% 1.17/1.00  --abstr_ref_sig_restrict                funpre
% 1.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.00  --abstr_ref_under                       []
% 1.17/1.00  
% 1.17/1.00  ------ SAT Options
% 1.17/1.00  
% 1.17/1.00  --sat_mode                              false
% 1.17/1.00  --sat_fm_restart_options                ""
% 1.17/1.00  --sat_gr_def                            false
% 1.17/1.00  --sat_epr_types                         true
% 1.17/1.00  --sat_non_cyclic_types                  false
% 1.17/1.00  --sat_finite_models                     false
% 1.17/1.00  --sat_fm_lemmas                         false
% 1.17/1.00  --sat_fm_prep                           false
% 1.17/1.00  --sat_fm_uc_incr                        true
% 1.17/1.00  --sat_out_model                         small
% 1.17/1.00  --sat_out_clauses                       false
% 1.17/1.00  
% 1.17/1.00  ------ QBF Options
% 1.17/1.00  
% 1.17/1.00  --qbf_mode                              false
% 1.17/1.00  --qbf_elim_univ                         false
% 1.17/1.00  --qbf_dom_inst                          none
% 1.17/1.00  --qbf_dom_pre_inst                      false
% 1.17/1.00  --qbf_sk_in                             false
% 1.17/1.00  --qbf_pred_elim                         true
% 1.17/1.00  --qbf_split                             512
% 1.17/1.00  
% 1.17/1.00  ------ BMC1 Options
% 1.17/1.00  
% 1.17/1.00  --bmc1_incremental                      false
% 1.17/1.00  --bmc1_axioms                           reachable_all
% 1.17/1.00  --bmc1_min_bound                        0
% 1.17/1.00  --bmc1_max_bound                        -1
% 1.17/1.00  --bmc1_max_bound_default                -1
% 1.17/1.00  --bmc1_symbol_reachability              true
% 1.17/1.00  --bmc1_property_lemmas                  false
% 1.17/1.00  --bmc1_k_induction                      false
% 1.17/1.00  --bmc1_non_equiv_states                 false
% 1.17/1.00  --bmc1_deadlock                         false
% 1.17/1.00  --bmc1_ucm                              false
% 1.17/1.00  --bmc1_add_unsat_core                   none
% 1.17/1.00  --bmc1_unsat_core_children              false
% 1.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.00  --bmc1_out_stat                         full
% 1.17/1.00  --bmc1_ground_init                      false
% 1.17/1.00  --bmc1_pre_inst_next_state              false
% 1.17/1.00  --bmc1_pre_inst_state                   false
% 1.17/1.00  --bmc1_pre_inst_reach_state             false
% 1.17/1.00  --bmc1_out_unsat_core                   false
% 1.17/1.00  --bmc1_aig_witness_out                  false
% 1.17/1.00  --bmc1_verbose                          false
% 1.17/1.00  --bmc1_dump_clauses_tptp                false
% 1.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.00  --bmc1_dump_file                        -
% 1.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.00  --bmc1_ucm_extend_mode                  1
% 1.17/1.00  --bmc1_ucm_init_mode                    2
% 1.17/1.00  --bmc1_ucm_cone_mode                    none
% 1.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.00  --bmc1_ucm_relax_model                  4
% 1.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.00  --bmc1_ucm_layered_model                none
% 1.17/1.00  --bmc1_ucm_max_lemma_size               10
% 1.17/1.00  
% 1.17/1.00  ------ AIG Options
% 1.17/1.00  
% 1.17/1.00  --aig_mode                              false
% 1.17/1.00  
% 1.17/1.00  ------ Instantiation Options
% 1.17/1.00  
% 1.17/1.00  --instantiation_flag                    true
% 1.17/1.00  --inst_sos_flag                         false
% 1.17/1.00  --inst_sos_phase                        true
% 1.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.00  --inst_lit_sel_side                     num_symb
% 1.17/1.00  --inst_solver_per_active                1400
% 1.17/1.00  --inst_solver_calls_frac                1.
% 1.17/1.00  --inst_passive_queue_type               priority_queues
% 1.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.00  --inst_passive_queues_freq              [25;2]
% 1.17/1.00  --inst_dismatching                      true
% 1.17/1.00  --inst_eager_unprocessed_to_passive     true
% 1.17/1.00  --inst_prop_sim_given                   true
% 1.17/1.00  --inst_prop_sim_new                     false
% 1.17/1.00  --inst_subs_new                         false
% 1.17/1.00  --inst_eq_res_simp                      false
% 1.17/1.00  --inst_subs_given                       false
% 1.17/1.00  --inst_orphan_elimination               true
% 1.17/1.00  --inst_learning_loop_flag               true
% 1.17/1.00  --inst_learning_start                   3000
% 1.17/1.00  --inst_learning_factor                  2
% 1.17/1.00  --inst_start_prop_sim_after_learn       3
% 1.17/1.00  --inst_sel_renew                        solver
% 1.17/1.00  --inst_lit_activity_flag                true
% 1.17/1.00  --inst_restr_to_given                   false
% 1.17/1.00  --inst_activity_threshold               500
% 1.17/1.00  --inst_out_proof                        true
% 1.17/1.00  
% 1.17/1.00  ------ Resolution Options
% 1.17/1.00  
% 1.17/1.00  --resolution_flag                       true
% 1.17/1.00  --res_lit_sel                           adaptive
% 1.17/1.00  --res_lit_sel_side                      none
% 1.17/1.00  --res_ordering                          kbo
% 1.17/1.00  --res_to_prop_solver                    active
% 1.17/1.00  --res_prop_simpl_new                    false
% 1.17/1.00  --res_prop_simpl_given                  true
% 1.17/1.00  --res_passive_queue_type                priority_queues
% 1.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.00  --res_passive_queues_freq               [15;5]
% 1.17/1.00  --res_forward_subs                      full
% 1.17/1.00  --res_backward_subs                     full
% 1.17/1.00  --res_forward_subs_resolution           true
% 1.17/1.00  --res_backward_subs_resolution          true
% 1.17/1.00  --res_orphan_elimination                true
% 1.17/1.00  --res_time_limit                        2.
% 1.17/1.00  --res_out_proof                         true
% 1.17/1.00  
% 1.17/1.00  ------ Superposition Options
% 1.17/1.00  
% 1.17/1.00  --superposition_flag                    true
% 1.17/1.00  --sup_passive_queue_type                priority_queues
% 1.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.00  --demod_completeness_check              fast
% 1.17/1.00  --demod_use_ground                      true
% 1.17/1.00  --sup_to_prop_solver                    passive
% 1.17/1.00  --sup_prop_simpl_new                    true
% 1.17/1.00  --sup_prop_simpl_given                  true
% 1.17/1.00  --sup_fun_splitting                     false
% 1.17/1.00  --sup_smt_interval                      50000
% 1.17/1.00  
% 1.17/1.00  ------ Superposition Simplification Setup
% 1.17/1.00  
% 1.17/1.00  --sup_indices_passive                   []
% 1.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_full_bw                           [BwDemod]
% 1.17/1.00  --sup_immed_triv                        [TrivRules]
% 1.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_immed_bw_main                     []
% 1.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.00  
% 1.17/1.00  ------ Combination Options
% 1.17/1.00  
% 1.17/1.00  --comb_res_mult                         3
% 1.17/1.00  --comb_sup_mult                         2
% 1.17/1.00  --comb_inst_mult                        10
% 1.17/1.00  
% 1.17/1.00  ------ Debug Options
% 1.17/1.00  
% 1.17/1.00  --dbg_backtrace                         false
% 1.17/1.00  --dbg_dump_prop_clauses                 false
% 1.17/1.00  --dbg_dump_prop_clauses_file            -
% 1.17/1.00  --dbg_out_stat                          false
% 1.17/1.00  ------ Parsing...
% 1.17/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.17/1.00  ------ Proving...
% 1.17/1.00  ------ Problem Properties 
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  clauses                                 12
% 1.17/1.00  conjectures                             3
% 1.17/1.00  EPR                                     1
% 1.17/1.00  Horn                                    12
% 1.17/1.00  unary                                   6
% 1.17/1.00  binary                                  3
% 1.17/1.00  lits                                    24
% 1.17/1.00  lits eq                                 4
% 1.17/1.00  fd_pure                                 0
% 1.17/1.00  fd_pseudo                               0
% 1.17/1.00  fd_cond                                 0
% 1.17/1.00  fd_pseudo_cond                          1
% 1.17/1.00  AC symbols                              0
% 1.17/1.00  
% 1.17/1.00  ------ Schedule dynamic 5 is on 
% 1.17/1.00  
% 1.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  ------ 
% 1.17/1.00  Current options:
% 1.17/1.00  ------ 
% 1.17/1.00  
% 1.17/1.00  ------ Input Options
% 1.17/1.00  
% 1.17/1.00  --out_options                           all
% 1.17/1.00  --tptp_safe_out                         true
% 1.17/1.00  --problem_path                          ""
% 1.17/1.00  --include_path                          ""
% 1.17/1.00  --clausifier                            res/vclausify_rel
% 1.17/1.00  --clausifier_options                    --mode clausify
% 1.17/1.00  --stdin                                 false
% 1.17/1.00  --stats_out                             all
% 1.17/1.00  
% 1.17/1.00  ------ General Options
% 1.17/1.00  
% 1.17/1.00  --fof                                   false
% 1.17/1.00  --time_out_real                         305.
% 1.17/1.00  --time_out_virtual                      -1.
% 1.17/1.00  --symbol_type_check                     false
% 1.17/1.00  --clausify_out                          false
% 1.17/1.00  --sig_cnt_out                           false
% 1.17/1.00  --trig_cnt_out                          false
% 1.17/1.00  --trig_cnt_out_tolerance                1.
% 1.17/1.00  --trig_cnt_out_sk_spl                   false
% 1.17/1.00  --abstr_cl_out                          false
% 1.17/1.00  
% 1.17/1.00  ------ Global Options
% 1.17/1.00  
% 1.17/1.00  --schedule                              default
% 1.17/1.00  --add_important_lit                     false
% 1.17/1.00  --prop_solver_per_cl                    1000
% 1.17/1.00  --min_unsat_core                        false
% 1.17/1.00  --soft_assumptions                      false
% 1.17/1.00  --soft_lemma_size                       3
% 1.17/1.00  --prop_impl_unit_size                   0
% 1.17/1.00  --prop_impl_unit                        []
% 1.17/1.00  --share_sel_clauses                     true
% 1.17/1.00  --reset_solvers                         false
% 1.17/1.00  --bc_imp_inh                            [conj_cone]
% 1.17/1.00  --conj_cone_tolerance                   3.
% 1.17/1.00  --extra_neg_conj                        none
% 1.17/1.00  --large_theory_mode                     true
% 1.17/1.00  --prolific_symb_bound                   200
% 1.17/1.00  --lt_threshold                          2000
% 1.17/1.00  --clause_weak_htbl                      true
% 1.17/1.00  --gc_record_bc_elim                     false
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing Options
% 1.17/1.00  
% 1.17/1.00  --preprocessing_flag                    true
% 1.17/1.00  --time_out_prep_mult                    0.1
% 1.17/1.00  --splitting_mode                        input
% 1.17/1.00  --splitting_grd                         true
% 1.17/1.00  --splitting_cvd                         false
% 1.17/1.00  --splitting_cvd_svl                     false
% 1.17/1.00  --splitting_nvd                         32
% 1.17/1.00  --sub_typing                            true
% 1.17/1.00  --prep_gs_sim                           true
% 1.17/1.00  --prep_unflatten                        true
% 1.17/1.00  --prep_res_sim                          true
% 1.17/1.00  --prep_upred                            true
% 1.17/1.00  --prep_sem_filter                       exhaustive
% 1.17/1.00  --prep_sem_filter_out                   false
% 1.17/1.00  --pred_elim                             true
% 1.17/1.00  --res_sim_input                         true
% 1.17/1.00  --eq_ax_congr_red                       true
% 1.17/1.00  --pure_diseq_elim                       true
% 1.17/1.00  --brand_transform                       false
% 1.17/1.00  --non_eq_to_eq                          false
% 1.17/1.00  --prep_def_merge                        true
% 1.17/1.00  --prep_def_merge_prop_impl              false
% 1.17/1.00  --prep_def_merge_mbd                    true
% 1.17/1.00  --prep_def_merge_tr_red                 false
% 1.17/1.00  --prep_def_merge_tr_cl                  false
% 1.17/1.00  --smt_preprocessing                     true
% 1.17/1.00  --smt_ac_axioms                         fast
% 1.17/1.00  --preprocessed_out                      false
% 1.17/1.00  --preprocessed_stats                    false
% 1.17/1.00  
% 1.17/1.00  ------ Abstraction refinement Options
% 1.17/1.00  
% 1.17/1.00  --abstr_ref                             []
% 1.17/1.00  --abstr_ref_prep                        false
% 1.17/1.00  --abstr_ref_until_sat                   false
% 1.17/1.00  --abstr_ref_sig_restrict                funpre
% 1.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.00  --abstr_ref_under                       []
% 1.17/1.00  
% 1.17/1.00  ------ SAT Options
% 1.17/1.00  
% 1.17/1.00  --sat_mode                              false
% 1.17/1.00  --sat_fm_restart_options                ""
% 1.17/1.00  --sat_gr_def                            false
% 1.17/1.00  --sat_epr_types                         true
% 1.17/1.00  --sat_non_cyclic_types                  false
% 1.17/1.00  --sat_finite_models                     false
% 1.17/1.00  --sat_fm_lemmas                         false
% 1.17/1.00  --sat_fm_prep                           false
% 1.17/1.00  --sat_fm_uc_incr                        true
% 1.17/1.00  --sat_out_model                         small
% 1.17/1.00  --sat_out_clauses                       false
% 1.17/1.00  
% 1.17/1.00  ------ QBF Options
% 1.17/1.00  
% 1.17/1.00  --qbf_mode                              false
% 1.17/1.00  --qbf_elim_univ                         false
% 1.17/1.00  --qbf_dom_inst                          none
% 1.17/1.00  --qbf_dom_pre_inst                      false
% 1.17/1.00  --qbf_sk_in                             false
% 1.17/1.00  --qbf_pred_elim                         true
% 1.17/1.00  --qbf_split                             512
% 1.17/1.00  
% 1.17/1.00  ------ BMC1 Options
% 1.17/1.00  
% 1.17/1.00  --bmc1_incremental                      false
% 1.17/1.00  --bmc1_axioms                           reachable_all
% 1.17/1.00  --bmc1_min_bound                        0
% 1.17/1.00  --bmc1_max_bound                        -1
% 1.17/1.00  --bmc1_max_bound_default                -1
% 1.17/1.00  --bmc1_symbol_reachability              true
% 1.17/1.00  --bmc1_property_lemmas                  false
% 1.17/1.00  --bmc1_k_induction                      false
% 1.17/1.00  --bmc1_non_equiv_states                 false
% 1.17/1.00  --bmc1_deadlock                         false
% 1.17/1.00  --bmc1_ucm                              false
% 1.17/1.00  --bmc1_add_unsat_core                   none
% 1.17/1.00  --bmc1_unsat_core_children              false
% 1.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.00  --bmc1_out_stat                         full
% 1.17/1.00  --bmc1_ground_init                      false
% 1.17/1.00  --bmc1_pre_inst_next_state              false
% 1.17/1.00  --bmc1_pre_inst_state                   false
% 1.17/1.00  --bmc1_pre_inst_reach_state             false
% 1.17/1.00  --bmc1_out_unsat_core                   false
% 1.17/1.00  --bmc1_aig_witness_out                  false
% 1.17/1.00  --bmc1_verbose                          false
% 1.17/1.00  --bmc1_dump_clauses_tptp                false
% 1.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.00  --bmc1_dump_file                        -
% 1.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.00  --bmc1_ucm_extend_mode                  1
% 1.17/1.00  --bmc1_ucm_init_mode                    2
% 1.17/1.00  --bmc1_ucm_cone_mode                    none
% 1.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.00  --bmc1_ucm_relax_model                  4
% 1.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.00  --bmc1_ucm_layered_model                none
% 1.17/1.00  --bmc1_ucm_max_lemma_size               10
% 1.17/1.00  
% 1.17/1.00  ------ AIG Options
% 1.17/1.00  
% 1.17/1.00  --aig_mode                              false
% 1.17/1.00  
% 1.17/1.00  ------ Instantiation Options
% 1.17/1.00  
% 1.17/1.00  --instantiation_flag                    true
% 1.17/1.00  --inst_sos_flag                         false
% 1.17/1.00  --inst_sos_phase                        true
% 1.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.00  --inst_lit_sel_side                     none
% 1.17/1.00  --inst_solver_per_active                1400
% 1.17/1.00  --inst_solver_calls_frac                1.
% 1.17/1.00  --inst_passive_queue_type               priority_queues
% 1.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.00  --inst_passive_queues_freq              [25;2]
% 1.17/1.00  --inst_dismatching                      true
% 1.17/1.00  --inst_eager_unprocessed_to_passive     true
% 1.17/1.00  --inst_prop_sim_given                   true
% 1.17/1.00  --inst_prop_sim_new                     false
% 1.17/1.00  --inst_subs_new                         false
% 1.17/1.00  --inst_eq_res_simp                      false
% 1.17/1.00  --inst_subs_given                       false
% 1.17/1.00  --inst_orphan_elimination               true
% 1.17/1.00  --inst_learning_loop_flag               true
% 1.17/1.00  --inst_learning_start                   3000
% 1.17/1.00  --inst_learning_factor                  2
% 1.17/1.00  --inst_start_prop_sim_after_learn       3
% 1.17/1.00  --inst_sel_renew                        solver
% 1.17/1.00  --inst_lit_activity_flag                true
% 1.17/1.00  --inst_restr_to_given                   false
% 1.17/1.00  --inst_activity_threshold               500
% 1.17/1.00  --inst_out_proof                        true
% 1.17/1.00  
% 1.17/1.00  ------ Resolution Options
% 1.17/1.00  
% 1.17/1.00  --resolution_flag                       false
% 1.17/1.00  --res_lit_sel                           adaptive
% 1.17/1.00  --res_lit_sel_side                      none
% 1.17/1.00  --res_ordering                          kbo
% 1.17/1.00  --res_to_prop_solver                    active
% 1.17/1.00  --res_prop_simpl_new                    false
% 1.17/1.00  --res_prop_simpl_given                  true
% 1.17/1.00  --res_passive_queue_type                priority_queues
% 1.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.00  --res_passive_queues_freq               [15;5]
% 1.17/1.00  --res_forward_subs                      full
% 1.17/1.00  --res_backward_subs                     full
% 1.17/1.00  --res_forward_subs_resolution           true
% 1.17/1.00  --res_backward_subs_resolution          true
% 1.17/1.00  --res_orphan_elimination                true
% 1.17/1.00  --res_time_limit                        2.
% 1.17/1.00  --res_out_proof                         true
% 1.17/1.00  
% 1.17/1.00  ------ Superposition Options
% 1.17/1.00  
% 1.17/1.00  --superposition_flag                    true
% 1.17/1.00  --sup_passive_queue_type                priority_queues
% 1.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.00  --demod_completeness_check              fast
% 1.17/1.00  --demod_use_ground                      true
% 1.17/1.00  --sup_to_prop_solver                    passive
% 1.17/1.00  --sup_prop_simpl_new                    true
% 1.17/1.00  --sup_prop_simpl_given                  true
% 1.17/1.00  --sup_fun_splitting                     false
% 1.17/1.00  --sup_smt_interval                      50000
% 1.17/1.00  
% 1.17/1.00  ------ Superposition Simplification Setup
% 1.17/1.00  
% 1.17/1.00  --sup_indices_passive                   []
% 1.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_full_bw                           [BwDemod]
% 1.17/1.00  --sup_immed_triv                        [TrivRules]
% 1.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_immed_bw_main                     []
% 1.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.00  
% 1.17/1.00  ------ Combination Options
% 1.17/1.00  
% 1.17/1.00  --comb_res_mult                         3
% 1.17/1.00  --comb_sup_mult                         2
% 1.17/1.00  --comb_inst_mult                        10
% 1.17/1.00  
% 1.17/1.00  ------ Debug Options
% 1.17/1.00  
% 1.17/1.00  --dbg_backtrace                         false
% 1.17/1.00  --dbg_dump_prop_clauses                 false
% 1.17/1.00  --dbg_dump_prop_clauses_file            -
% 1.17/1.00  --dbg_out_stat                          false
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  ------ Proving...
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  % SZS status Theorem for theBenchmark.p
% 1.17/1.00  
% 1.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/1.00  
% 1.17/1.00  fof(f1,axiom,(
% 1.17/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f12,plain,(
% 1.17/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.17/1.00    inference(pure_predicate_removal,[],[f1])).
% 1.17/1.00  
% 1.17/1.00  fof(f13,plain,(
% 1.17/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.17/1.00    inference(pure_predicate_removal,[],[f12])).
% 1.17/1.00  
% 1.17/1.00  fof(f14,plain,(
% 1.17/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.17/1.00    inference(ennf_transformation,[],[f13])).
% 1.17/1.00  
% 1.17/1.00  fof(f15,plain,(
% 1.17/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.17/1.00    inference(flattening,[],[f14])).
% 1.17/1.00  
% 1.17/1.00  fof(f41,plain,(
% 1.17/1.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f15])).
% 1.17/1.00  
% 1.17/1.00  fof(f2,axiom,(
% 1.17/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f11,plain,(
% 1.17/1.00    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.17/1.00    inference(pure_predicate_removal,[],[f2])).
% 1.17/1.00  
% 1.17/1.00  fof(f16,plain,(
% 1.17/1.00    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.17/1.00    inference(ennf_transformation,[],[f11])).
% 1.17/1.00  
% 1.17/1.00  fof(f45,plain,(
% 1.17/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f16])).
% 1.17/1.00  
% 1.17/1.00  fof(f4,axiom,(
% 1.17/1.00    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f19,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f4])).
% 1.17/1.00  
% 1.17/1.00  fof(f20,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f19])).
% 1.17/1.00  
% 1.17/1.00  fof(f48,plain,(
% 1.17/1.00    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f20])).
% 1.17/1.00  
% 1.17/1.00  fof(f9,conjecture,(
% 1.17/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f10,negated_conjecture,(
% 1.17/1.00    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.17/1.00    inference(negated_conjecture,[],[f9])).
% 1.17/1.00  
% 1.17/1.00  fof(f29,plain,(
% 1.17/1.00    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f10])).
% 1.17/1.00  
% 1.17/1.00  fof(f30,plain,(
% 1.17/1.00    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f29])).
% 1.17/1.00  
% 1.17/1.00  fof(f38,plain,(
% 1.17/1.00    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK3) != X1 & r3_lattice3(X0,X1,sK3) & r2_hidden(X1,sK3))) )),
% 1.17/1.00    introduced(choice_axiom,[])).
% 1.17/1.00  
% 1.17/1.00  fof(f37,plain,(
% 1.17/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK2 & r3_lattice3(X0,sK2,X2) & r2_hidden(sK2,X2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.17/1.00    introduced(choice_axiom,[])).
% 1.17/1.00  
% 1.17/1.00  fof(f36,plain,(
% 1.17/1.00    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK1,X2) != X1 & r3_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 1.17/1.00    introduced(choice_axiom,[])).
% 1.17/1.00  
% 1.17/1.00  fof(f39,plain,(
% 1.17/1.00    ((k16_lattice3(sK1,sK3) != sK2 & r3_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 1.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f38,f37,f36])).
% 1.17/1.00  
% 1.17/1.00  fof(f58,plain,(
% 1.17/1.00    v10_lattices(sK1)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f57,plain,(
% 1.17/1.00    ~v2_struct_0(sK1)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f60,plain,(
% 1.17/1.00    l3_lattices(sK1)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f8,axiom,(
% 1.17/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f27,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f8])).
% 1.17/1.00  
% 1.17/1.00  fof(f28,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f27])).
% 1.17/1.00  
% 1.17/1.00  fof(f55,plain,(
% 1.17/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f28])).
% 1.17/1.00  
% 1.17/1.00  fof(f59,plain,(
% 1.17/1.00    v4_lattice3(sK1)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f3,axiom,(
% 1.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f17,plain,(
% 1.17/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f3])).
% 1.17/1.00  
% 1.17/1.00  fof(f18,plain,(
% 1.17/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f17])).
% 1.17/1.00  
% 1.17/1.00  fof(f31,plain,(
% 1.17/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(nnf_transformation,[],[f18])).
% 1.17/1.00  
% 1.17/1.00  fof(f46,plain,(
% 1.17/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f31])).
% 1.17/1.00  
% 1.17/1.00  fof(f44,plain,(
% 1.17/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f15])).
% 1.17/1.00  
% 1.17/1.00  fof(f42,plain,(
% 1.17/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f15])).
% 1.17/1.00  
% 1.17/1.00  fof(f43,plain,(
% 1.17/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f15])).
% 1.17/1.00  
% 1.17/1.00  fof(f56,plain,(
% 1.17/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f28])).
% 1.17/1.00  
% 1.17/1.00  fof(f6,axiom,(
% 1.17/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f23,plain,(
% 1.17/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f6])).
% 1.17/1.00  
% 1.17/1.00  fof(f24,plain,(
% 1.17/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f23])).
% 1.17/1.00  
% 1.17/1.00  fof(f50,plain,(
% 1.17/1.00    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f24])).
% 1.17/1.00  
% 1.17/1.00  fof(f5,axiom,(
% 1.17/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f21,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.17/1.00    inference(ennf_transformation,[],[f5])).
% 1.17/1.00  
% 1.17/1.00  fof(f22,plain,(
% 1.17/1.00    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.17/1.00    inference(flattening,[],[f21])).
% 1.17/1.00  
% 1.17/1.00  fof(f49,plain,(
% 1.17/1.00    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f22])).
% 1.17/1.00  
% 1.17/1.00  fof(f64,plain,(
% 1.17/1.00    k16_lattice3(sK1,sK3) != sK2),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f7,axiom,(
% 1.17/1.00    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.00  
% 1.17/1.00  fof(f25,plain,(
% 1.17/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 1.17/1.00    inference(ennf_transformation,[],[f7])).
% 1.17/1.00  
% 1.17/1.00  fof(f26,plain,(
% 1.17/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.17/1.00    inference(flattening,[],[f25])).
% 1.17/1.00  
% 1.17/1.00  fof(f32,plain,(
% 1.17/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.17/1.00    inference(nnf_transformation,[],[f26])).
% 1.17/1.00  
% 1.17/1.00  fof(f33,plain,(
% 1.17/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.17/1.00    inference(rectify,[],[f32])).
% 1.17/1.00  
% 1.17/1.00  fof(f34,plain,(
% 1.17/1.00    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK0(X0,X1,X2),X2) & sK0(X0,X1,X2) = X0 & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))))),
% 1.17/1.00    introduced(choice_axiom,[])).
% 1.17/1.00  
% 1.17/1.00  fof(f35,plain,(
% 1.17/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK0(X0,X1,X2),X2) & sK0(X0,X1,X2) = X0 & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 1.17/1.00  
% 1.17/1.00  fof(f54,plain,(
% 1.17/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.17/1.00    inference(cnf_transformation,[],[f35])).
% 1.17/1.00  
% 1.17/1.00  fof(f65,plain,(
% 1.17/1.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.17/1.00    inference(equality_resolution,[],[f54])).
% 1.17/1.00  
% 1.17/1.00  fof(f63,plain,(
% 1.17/1.00    r3_lattice3(sK1,sK2,sK3)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f62,plain,(
% 1.17/1.00    r2_hidden(sK2,sK3)),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  fof(f61,plain,(
% 1.17/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.17/1.00    inference(cnf_transformation,[],[f39])).
% 1.17/1.00  
% 1.17/1.00  cnf(c_3,plain,
% 1.17/1.00      ( v4_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_5,plain,
% 1.17/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_8,plain,
% 1.17/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r1_lattices(X0,X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ l2_lattices(X0)
% 1.17/1.00      | ~ v4_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | X2 = X1 ),
% 1.17/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_259,plain,
% 1.17/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r1_lattices(X0,X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ v4_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | X2 = X1 ),
% 1.17/1.00      inference(resolution,[status(thm)],[c_5,c_8]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_297,plain,
% 1.17/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r1_lattices(X0,X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0)
% 1.17/1.00      | X2 = X1 ),
% 1.17/1.00      inference(resolution,[status(thm)],[c_3,c_259]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_23,negated_conjecture,
% 1.17/1.00      ( v10_lattices(sK1) ),
% 1.17/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_427,plain,
% 1.17/1.00      ( ~ r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r1_lattices(X0,X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | X2 = X1
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_297,c_23]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_428,plain,
% 1.17/1.00      ( ~ r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r1_lattices(sK1,X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | X0 = X1 ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_24,negated_conjecture,
% 1.17/1.00      ( ~ v2_struct_0(sK1) ),
% 1.17/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_21,negated_conjecture,
% 1.17/1.00      ( l3_lattices(sK1) ),
% 1.17/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_432,plain,
% 1.17/1.00      ( ~ r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r1_lattices(sK1,X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | X0 = X1 ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_428,c_24,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_779,plain,
% 1.17/1.00      ( ~ r1_lattices(sK1,X0_51,X1_51)
% 1.17/1.00      | ~ r1_lattices(sK1,X1_51,X0_51)
% 1.17/1.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.17/1.00      | X0_51 = X1_51 ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_432]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1417,plain,
% 1.17/1.00      ( ~ r1_lattices(sK1,X0_51,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)))
% 1.17/1.00      | ~ r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),X0_51)
% 1.17/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1))
% 1.17/1.00      | X0_51 = k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_779]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1419,plain,
% 1.17/1.00      ( ~ r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),sK2)
% 1.17/1.00      | ~ r1_lattices(sK1,sK2,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.17/1.00      | sK2 = k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_786,plain,
% 1.17/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.17/1.00      theory(equality) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1080,plain,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) != X0_51
% 1.17/1.00      | k16_lattice3(sK1,sK3) = sK2
% 1.17/1.00      | sK2 != X0_51 ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_786]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1315,plain,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) != k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52))
% 1.17/1.00      | k16_lattice3(sK1,sK3) = sK2
% 1.17/1.00      | sK2 != k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1080]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1316,plain,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) != k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3))
% 1.17/1.00      | k16_lattice3(sK1,sK3) = sK2
% 1.17/1.00      | sK2 != k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1315]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1100,plain,
% 1.17/1.00      ( X0_51 != X1_51
% 1.17/1.00      | k16_lattice3(sK1,sK3) != X1_51
% 1.17/1.00      | k16_lattice3(sK1,sK3) = X0_51 ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_786]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1171,plain,
% 1.17/1.00      ( X0_51 != k16_lattice3(sK1,sK3)
% 1.17/1.00      | k16_lattice3(sK1,sK3) = X0_51
% 1.17/1.00      | k16_lattice3(sK1,sK3) != k16_lattice3(sK1,sK3) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1100]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1283,plain,
% 1.17/1.00      ( k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3)
% 1.17/1.00      | k16_lattice3(sK1,sK3) = k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3))
% 1.17/1.00      | k16_lattice3(sK1,sK3) != k16_lattice3(sK1,sK3) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1171]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_16,plain,
% 1.17/1.00      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 1.17/1.00      | ~ r2_hidden(X1,X2)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ v4_lattice3(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_22,negated_conjecture,
% 1.17/1.00      ( v4_lattice3(sK1) ),
% 1.17/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_377,plain,
% 1.17/1.00      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 1.17/1.00      | ~ r2_hidden(X1,X2)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_378,plain,
% 1.17/1.00      ( r3_lattices(sK1,X0,k15_lattice3(sK1,X1))
% 1.17/1.00      | ~ r2_hidden(X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | ~ v10_lattices(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_377]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_382,plain,
% 1.17/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ r2_hidden(X0,X1)
% 1.17/1.00      | r3_lattices(sK1,X0,k15_lattice3(sK1,X1)) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_378,c_24,c_23,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_383,plain,
% 1.17/1.00      ( r3_lattices(sK1,X0,k15_lattice3(sK1,X1))
% 1.17/1.00      | ~ r2_hidden(X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(renaming,[status(thm)],[c_382]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_7,plain,
% 1.17/1.00      ( r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r3_lattices(X0,X1,X2)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ v6_lattices(X0)
% 1.17/1.00      | ~ v8_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v9_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_0,plain,
% 1.17/1.00      ( ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0)
% 1.17/1.00      | v9_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_476,plain,
% 1.17/1.00      ( ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | v9_lattices(X0)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_477,plain,
% 1.17/1.00      ( ~ l3_lattices(sK1) | v2_struct_0(sK1) | v9_lattices(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_79,plain,
% 1.17/1.00      ( ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | ~ v10_lattices(sK1)
% 1.17/1.00      | v9_lattices(sK1) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_479,plain,
% 1.17/1.00      ( v9_lattices(sK1) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_477,c_24,c_23,c_21,c_79]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_499,plain,
% 1.17/1.00      ( r1_lattices(X0,X1,X2)
% 1.17/1.00      | ~ r3_lattices(X0,X1,X2)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ v6_lattices(X0)
% 1.17/1.00      | ~ v8_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_479]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_500,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r3_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ v6_lattices(sK1)
% 1.17/1.00      | ~ v8_lattices(sK1)
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_499]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_2,plain,
% 1.17/1.00      ( v6_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_73,plain,
% 1.17/1.00      ( v6_lattices(sK1)
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | ~ v10_lattices(sK1) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1,plain,
% 1.17/1.00      ( v8_lattices(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_76,plain,
% 1.17/1.00      ( v8_lattices(sK1)
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | ~ v10_lattices(sK1) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_504,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r3_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_500,c_24,c_23,c_21,c_73,c_76]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_505,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r3_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(renaming,[status(thm)],[c_504]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_650,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r2_hidden(X2,X3)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | X0 != X2
% 1.17/1.00      | k15_lattice3(sK1,X3) != X1
% 1.17/1.00      | sK1 != sK1 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_383,c_505]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_651,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,k15_lattice3(sK1,X1))
% 1.17/1.00      | ~ r2_hidden(X0,X1)
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,X1),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_650]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_773,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0_51,k15_lattice3(sK1,X0_52))
% 1.17/1.00      | ~ r2_hidden(X0_51,X0_52)
% 1.17/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,X0_52),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_651]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1257,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0_51,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)))
% 1.17/1.00      | ~ r2_hidden(X0_51,a_2_1_lattice3(sK1,X0_52))
% 1.17/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1259,plain,
% 1.17/1.00      ( r1_lattices(sK1,sK2,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)))
% 1.17/1.00      | ~ r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
% 1.17/1.00      | ~ m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1257]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_788,plain,
% 1.17/1.00      ( ~ m1_subset_1(X0_51,X0_53)
% 1.17/1.00      | m1_subset_1(X1_51,X0_53)
% 1.17/1.00      | X1_51 != X0_51 ),
% 1.17/1.00      theory(equality) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1087,plain,
% 1.17/1.00      ( m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1))
% 1.17/1.00      | X0_51 != k16_lattice3(sK1,X0_52) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_788]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1112,plain,
% 1.17/1.00      ( m1_subset_1(k15_lattice3(sK1,X0_52),u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k16_lattice3(sK1,X1_52),u1_struct_0(sK1))
% 1.17/1.00      | k15_lattice3(sK1,X0_52) != k16_lattice3(sK1,X1_52) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1087]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1221,plain,
% 1.17/1.00      ( m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1))
% 1.17/1.00      | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) != k16_lattice3(sK1,X0_52) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1112]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1223,plain,
% 1.17/1.00      ( m1_subset_1(k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
% 1.17/1.00      | k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1221]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_787,plain,
% 1.17/1.00      ( ~ r1_lattices(X0_50,X0_51,X1_51)
% 1.17/1.00      | r1_lattices(X0_50,X2_51,X3_51)
% 1.17/1.00      | X2_51 != X0_51
% 1.17/1.00      | X3_51 != X1_51 ),
% 1.17/1.00      theory(equality) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1090,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0_51,X1_51)
% 1.17/1.00      | ~ r1_lattices(sK1,k16_lattice3(sK1,X0_52),X2_51)
% 1.17/1.00      | X1_51 != X2_51
% 1.17/1.00      | X0_51 != k16_lattice3(sK1,X0_52) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1134,plain,
% 1.17/1.00      ( r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)),X0_51)
% 1.17/1.00      | ~ r1_lattices(sK1,k16_lattice3(sK1,X0_52),X1_51)
% 1.17/1.00      | X0_51 != X1_51
% 1.17/1.00      | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) != k16_lattice3(sK1,X0_52) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1136,plain,
% 1.17/1.00      ( r1_lattices(sK1,k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)),sK2)
% 1.17/1.00      | ~ r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.17/1.00      | k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) != k16_lattice3(sK1,sK3)
% 1.17/1.00      | sK2 != sK2 ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_1134]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_785,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_1099,plain,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) = k16_lattice3(sK1,sK3) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_785]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_15,plain,
% 1.17/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.17/1.00      | ~ r2_hidden(X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ v4_lattice3(X0)
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_398,plain,
% 1.17/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.17/1.00      | ~ r2_hidden(X2,X1)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | ~ v10_lattices(X0)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_399,plain,
% 1.17/1.00      ( r3_lattices(sK1,k16_lattice3(sK1,X0),X1)
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1)
% 1.17/1.00      | ~ v10_lattices(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_403,plain,
% 1.17/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | r3_lattices(sK1,k16_lattice3(sK1,X0),X1) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_399,c_24,c_23,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_404,plain,
% 1.17/1.00      ( r3_lattices(sK1,k16_lattice3(sK1,X0),X1)
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(renaming,[status(thm)],[c_403]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_668,plain,
% 1.17/1.00      ( r1_lattices(sK1,X0,X1)
% 1.17/1.00      | ~ r2_hidden(X2,X3)
% 1.17/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | X1 != X2
% 1.17/1.00      | k16_lattice3(sK1,X3) != X0
% 1.17/1.00      | sK1 != sK1 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_404,c_505]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_669,plain,
% 1.17/1.00      ( r1_lattices(sK1,k16_lattice3(sK1,X0),X1)
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_668]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_10,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_557,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_558,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1))
% 1.17/1.00      | ~ l3_lattices(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_557]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_673,plain,
% 1.17/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | r1_lattices(sK1,k16_lattice3(sK1,X0),X1) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_669,c_21,c_558]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_674,plain,
% 1.17/1.00      ( r1_lattices(sK1,k16_lattice3(sK1,X0),X1)
% 1.17/1.00      | ~ r2_hidden(X1,X0)
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(renaming,[status(thm)],[c_673]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_772,plain,
% 1.17/1.00      ( r1_lattices(sK1,k16_lattice3(sK1,X0_52),X0_51)
% 1.17/1.00      | ~ r2_hidden(X0_51,X0_52)
% 1.17/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_674]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_816,plain,
% 1.17/1.00      ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.17/1.00      | ~ r2_hidden(sK2,sK3)
% 1.17/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_772]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_9,plain,
% 1.17/1.00      ( ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0)
% 1.17/1.00      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1) ),
% 1.17/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_572,plain,
% 1.17/1.00      ( ~ l3_lattices(X0)
% 1.17/1.00      | k15_lattice3(X0,a_2_1_lattice3(X0,X1)) = k16_lattice3(X0,X1)
% 1.17/1.00      | sK1 != X0 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_573,plain,
% 1.17/1.00      ( ~ l3_lattices(sK1)
% 1.17/1.00      | k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_572]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_577,plain,
% 1.17/1.00      ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0)) = k16_lattice3(sK1,X0) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_573,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_777,plain,
% 1.17/1.00      ( k15_lattice3(sK1,a_2_1_lattice3(sK1,X0_52)) = k16_lattice3(sK1,X0_52) ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_577]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_802,plain,
% 1.17/1.00      ( k15_lattice3(sK1,a_2_1_lattice3(sK1,sK3)) = k16_lattice3(sK1,sK3) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_562,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(global_propositional_subsumption,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_558,c_21]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_778,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(sK1,X0_52),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_562]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_800,plain,
% 1.17/1.00      ( m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_778]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_17,negated_conjecture,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) != sK2 ),
% 1.17/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_783,negated_conjecture,
% 1.17/1.00      ( k16_lattice3(sK1,sK3) != sK2 ),
% 1.17/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_794,plain,
% 1.17/1.00      ( sK2 = sK2 ),
% 1.17/1.00      inference(instantiation,[status(thm)],[c_785]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_11,plain,
% 1.17/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 1.17/1.00      | r2_hidden(X1,a_2_1_lattice3(X0,X2))
% 1.17/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.17/1.00      | ~ l3_lattices(X0)
% 1.17/1.00      | v2_struct_0(X0) ),
% 1.17/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_18,negated_conjecture,
% 1.17/1.00      ( r3_lattice3(sK1,sK2,sK3) ),
% 1.17/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_359,plain,
% 1.17/1.00      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
% 1.17/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.17/1.00      | ~ l3_lattices(X1)
% 1.17/1.00      | v2_struct_0(X1)
% 1.17/1.00      | sK2 != X0
% 1.17/1.00      | sK3 != X2
% 1.17/1.00      | sK1 != X1 ),
% 1.17/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_360,plain,
% 1.17/1.00      ( r2_hidden(sK2,a_2_1_lattice3(sK1,sK3))
% 1.17/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.17/1.00      | ~ l3_lattices(sK1)
% 1.17/1.00      | v2_struct_0(sK1) ),
% 1.17/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_19,negated_conjecture,
% 1.17/1.00      ( r2_hidden(sK2,sK3) ),
% 1.17/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(c_20,negated_conjecture,
% 1.17/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.17/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.17/1.00  
% 1.17/1.00  cnf(contradiction,plain,
% 1.17/1.00      ( $false ),
% 1.17/1.00      inference(minisat,
% 1.17/1.00                [status(thm)],
% 1.17/1.00                [c_1419,c_1316,c_1283,c_1259,c_1223,c_1136,c_1099,c_816,
% 1.17/1.00                 c_802,c_800,c_783,c_794,c_360,c_19,c_20,c_21,c_24]) ).
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/1.00  
% 1.17/1.00  ------                               Statistics
% 1.17/1.00  
% 1.17/1.00  ------ General
% 1.17/1.00  
% 1.17/1.00  abstr_ref_over_cycles:                  0
% 1.17/1.00  abstr_ref_under_cycles:                 0
% 1.17/1.00  gc_basic_clause_elim:                   0
% 1.17/1.00  forced_gc_time:                         0
% 1.17/1.00  parsing_time:                           0.006
% 1.17/1.00  unif_index_cands_time:                  0.
% 1.17/1.00  unif_index_add_time:                    0.
% 1.17/1.00  orderings_time:                         0.
% 1.17/1.00  out_proof_time:                         0.009
% 1.17/1.00  total_time:                             0.06
% 1.17/1.00  num_of_symbols:                         54
% 1.17/1.00  num_of_terms:                           1296
% 1.17/1.00  
% 1.17/1.00  ------ Preprocessing
% 1.17/1.00  
% 1.17/1.00  num_of_splits:                          0
% 1.17/1.00  num_of_split_atoms:                     0
% 1.17/1.00  num_of_reused_defs:                     0
% 1.17/1.00  num_eq_ax_congr_red:                    30
% 1.17/1.00  num_of_sem_filtered_clauses:            1
% 1.17/1.00  num_of_subtypes:                        4
% 1.17/1.00  monotx_restored_types:                  0
% 1.17/1.00  sat_num_of_epr_types:                   0
% 1.17/1.00  sat_num_of_non_cyclic_types:            0
% 1.17/1.00  sat_guarded_non_collapsed_types:        1
% 1.17/1.00  num_pure_diseq_elim:                    0
% 1.17/1.00  simp_replaced_by:                       0
% 1.17/1.00  res_preprocessed:                       71
% 1.17/1.00  prep_upred:                             0
% 1.17/1.00  prep_unflattend:                        23
% 1.17/1.00  smt_new_axioms:                         0
% 1.17/1.00  pred_elim_cands:                        3
% 1.17/1.00  pred_elim:                              11
% 1.17/1.00  pred_elim_cl:                           12
% 1.17/1.00  pred_elim_cycles:                       13
% 1.17/1.00  merged_defs:                            0
% 1.17/1.00  merged_defs_ncl:                        0
% 1.17/1.00  bin_hyper_res:                          0
% 1.17/1.00  prep_cycles:                            4
% 1.17/1.00  pred_elim_time:                         0.006
% 1.17/1.00  splitting_time:                         0.
% 1.17/1.00  sem_filter_time:                        0.
% 1.17/1.00  monotx_time:                            0.
% 1.17/1.00  subtype_inf_time:                       0.
% 1.17/1.00  
% 1.17/1.00  ------ Problem properties
% 1.17/1.00  
% 1.17/1.00  clauses:                                12
% 1.17/1.00  conjectures:                            3
% 1.17/1.00  epr:                                    1
% 1.17/1.00  horn:                                   12
% 1.17/1.00  ground:                                 4
% 1.17/1.00  unary:                                  6
% 1.17/1.00  binary:                                 3
% 1.17/1.00  lits:                                   24
% 1.17/1.00  lits_eq:                                4
% 1.17/1.00  fd_pure:                                0
% 1.17/1.00  fd_pseudo:                              0
% 1.17/1.00  fd_cond:                                0
% 1.17/1.00  fd_pseudo_cond:                         1
% 1.17/1.00  ac_symbols:                             0
% 1.17/1.00  
% 1.17/1.00  ------ Propositional Solver
% 1.17/1.00  
% 1.17/1.00  prop_solver_calls:                      25
% 1.17/1.00  prop_fast_solver_calls:                 527
% 1.17/1.00  smt_solver_calls:                       0
% 1.17/1.00  smt_fast_solver_calls:                  0
% 1.17/1.00  prop_num_of_clauses:                    401
% 1.17/1.00  prop_preprocess_simplified:             2152
% 1.17/1.00  prop_fo_subsumed:                       32
% 1.17/1.00  prop_solver_time:                       0.
% 1.17/1.00  smt_solver_time:                        0.
% 1.17/1.00  smt_fast_solver_time:                   0.
% 1.17/1.00  prop_fast_solver_time:                  0.
% 1.17/1.00  prop_unsat_core_time:                   0.
% 1.17/1.00  
% 1.17/1.00  ------ QBF
% 1.17/1.00  
% 1.17/1.00  qbf_q_res:                              0
% 1.17/1.00  qbf_num_tautologies:                    0
% 1.17/1.00  qbf_prep_cycles:                        0
% 1.17/1.00  
% 1.17/1.00  ------ BMC1
% 1.17/1.00  
% 1.17/1.00  bmc1_current_bound:                     -1
% 1.17/1.00  bmc1_last_solved_bound:                 -1
% 1.17/1.00  bmc1_unsat_core_size:                   -1
% 1.17/1.00  bmc1_unsat_core_parents_size:           -1
% 1.17/1.00  bmc1_merge_next_fun:                    0
% 1.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.17/1.00  
% 1.17/1.00  ------ Instantiation
% 1.17/1.00  
% 1.17/1.00  inst_num_of_clauses:                    79
% 1.17/1.00  inst_num_in_passive:                    5
% 1.17/1.00  inst_num_in_active:                     51
% 1.17/1.00  inst_num_in_unprocessed:                22
% 1.17/1.00  inst_num_of_loops:                      54
% 1.17/1.00  inst_num_of_learning_restarts:          0
% 1.17/1.00  inst_num_moves_active_passive:          0
% 1.17/1.00  inst_lit_activity:                      0
% 1.17/1.00  inst_lit_activity_moves:                0
% 1.17/1.00  inst_num_tautologies:                   0
% 1.17/1.00  inst_num_prop_implied:                  0
% 1.17/1.00  inst_num_existing_simplified:           0
% 1.17/1.00  inst_num_eq_res_simplified:             0
% 1.17/1.00  inst_num_child_elim:                    0
% 1.17/1.00  inst_num_of_dismatching_blockings:      16
% 1.17/1.00  inst_num_of_non_proper_insts:           74
% 1.17/1.00  inst_num_of_duplicates:                 0
% 1.17/1.00  inst_inst_num_from_inst_to_res:         0
% 1.17/1.00  inst_dismatching_checking_time:         0.
% 1.17/1.00  
% 1.17/1.00  ------ Resolution
% 1.17/1.00  
% 1.17/1.00  res_num_of_clauses:                     0
% 1.17/1.00  res_num_in_passive:                     0
% 1.17/1.00  res_num_in_active:                      0
% 1.17/1.00  res_num_of_loops:                       75
% 1.17/1.00  res_forward_subset_subsumed:            4
% 1.17/1.00  res_backward_subset_subsumed:           0
% 1.17/1.00  res_forward_subsumed:                   0
% 1.17/1.00  res_backward_subsumed:                  0
% 1.17/1.00  res_forward_subsumption_resolution:     0
% 1.17/1.00  res_backward_subsumption_resolution:    0
% 1.17/1.00  res_clause_to_clause_subsumption:       21
% 1.17/1.00  res_orphan_elimination:                 0
% 1.17/1.00  res_tautology_del:                      9
% 1.17/1.00  res_num_eq_res_simplified:              0
% 1.17/1.00  res_num_sel_changes:                    0
% 1.17/1.00  res_moves_from_active_to_pass:          0
% 1.17/1.00  
% 1.17/1.00  ------ Superposition
% 1.17/1.00  
% 1.17/1.00  sup_time_total:                         0.
% 1.17/1.00  sup_time_generating:                    0.
% 1.17/1.00  sup_time_sim_full:                      0.
% 1.17/1.00  sup_time_sim_immed:                     0.
% 1.17/1.00  
% 1.17/1.00  sup_num_of_clauses:                     18
% 1.17/1.00  sup_num_in_active:                      10
% 1.17/1.00  sup_num_in_passive:                     8
% 1.17/1.00  sup_num_of_loops:                       10
% 1.17/1.00  sup_fw_superposition:                   7
% 1.17/1.00  sup_bw_superposition:                   0
% 1.17/1.00  sup_immediate_simplified:               0
% 1.17/1.00  sup_given_eliminated:                   0
% 1.17/1.00  comparisons_done:                       0
% 1.17/1.00  comparisons_avoided:                    0
% 1.17/1.00  
% 1.17/1.00  ------ Simplifications
% 1.17/1.00  
% 1.17/1.00  
% 1.17/1.00  sim_fw_subset_subsumed:                 0
% 1.17/1.00  sim_bw_subset_subsumed:                 0
% 1.17/1.00  sim_fw_subsumed:                        0
% 1.17/1.00  sim_bw_subsumed:                        0
% 1.17/1.00  sim_fw_subsumption_res:                 0
% 1.17/1.00  sim_bw_subsumption_res:                 0
% 1.17/1.00  sim_tautology_del:                      0
% 1.17/1.00  sim_eq_tautology_del:                   1
% 1.17/1.00  sim_eq_res_simp:                        0
% 1.17/1.00  sim_fw_demodulated:                     0
% 1.17/1.00  sim_bw_demodulated:                     0
% 1.17/1.00  sim_light_normalised:                   0
% 1.17/1.00  sim_joinable_taut:                      0
% 1.17/1.00  sim_joinable_simp:                      0
% 1.17/1.00  sim_ac_normalised:                      0
% 1.17/1.00  sim_smt_subsumption:                    0
% 1.17/1.00  
%------------------------------------------------------------------------------
