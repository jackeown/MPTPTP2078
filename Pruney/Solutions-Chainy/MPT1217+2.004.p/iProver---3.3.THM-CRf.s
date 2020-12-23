%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:23 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 891 expanded)
%              Number of clauses        :   88 ( 221 expanded)
%              Number of leaves         :   13 ( 283 expanded)
%              Depth                    :   22
%              Number of atoms          :  575 (5716 expanded)
%              Number of equality atoms :  127 ( 218 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1))
            & r3_lattices(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
       => ( v8_lattices(X0)
          & v7_lattices(X0)
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
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_519,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_672,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_518,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_673,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_13,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_373,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_13])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_677,plain,
    ( m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_15,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_16,c_15,c_13])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) = k7_lattices(sK0,k3_lattices(sK0,X1,X0)) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X1_44),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_674,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_44),k7_lattices(sK0,X1_44)) = k7_lattices(sK0,k3_lattices(sK0,X0_44,X1_44))
    | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_922,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,X0_44)),k7_lattices(sK0,X1_44)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,X0_44),X1_44))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_674])).

cnf(c_1982,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_922])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_16,c_15,c_13])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_675,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_782,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_673,c_675])).

cnf(c_1992,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),X0_44)) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1982,c_782])).

cnf(c_2119,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_672,c_1992])).

cnf(c_781,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_672,c_675])).

cnf(c_10,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_263,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_264,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_16,c_15,c_13])).

cnf(c_269,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) = k5_lattices(sK0)
    | k7_lattices(sK0,X0) != sK2
    | sK1 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_269])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,X0) = k5_lattices(sK0)
    | k7_lattices(sK0,X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,X0) = k5_lattices(sK0)
    | k7_lattices(sK0,X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_12])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,X0_44) = k5_lattices(sK0)
    | k7_lattices(sK0,X0_44) != sK2 ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_679,plain,
    ( k4_lattices(sK0,sK1,X0_44) = k5_lattices(sK0)
    | k7_lattices(sK0,X0_44) != sK2
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_858,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_679])).

cnf(c_739,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_742,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_743,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | k7_lattices(sK0,k7_lattices(sK0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_1441,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_11,c_739,c_742,c_743])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v4_lattices(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_178])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_15])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_16,c_13])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X1,X0) = k3_lattices(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
    | k3_lattices(sK0,X1_44,X0_44) = k3_lattices(sK0,X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_676,plain,
    ( k3_lattices(sK0,X0_44,X1_44) = k3_lattices(sK0,X1_44,X0_44)
    | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_1144,plain,
    ( k3_lattices(sK0,X0_44,sK2) = k3_lattices(sK0,sK2,X0_44)
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_676])).

cnf(c_1204,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,X0_44),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_1144])).

cnf(c_1448,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_673,c_1204])).

cnf(c_920,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,sK2,X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_674])).

cnf(c_949,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,X0_44))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,X0_44)))
    | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_920])).

cnf(c_1866,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_673,c_949])).

cnf(c_1873,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(light_normalisation,[status(thm)],[c_1866,c_782])).

cnf(c_2130,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2119,c_1441,c_1448,c_1873])).

cnf(c_9,negated_conjecture,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_239,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_240,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_16,c_15,c_13])).

cnf(c_245,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1)
    | k7_lattices(sK0,sK2) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_245])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_44) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_44) != k7_lattices(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_546,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0)
    | k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_521,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_530,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_524,plain,
    ( X0_44 != X1_44
    | k7_lattices(X0_45,X0_44) = k7_lattices(X0_45,X1_44) ),
    theory(equality)).

cnf(c_527,plain,
    ( k7_lattices(sK0,sK1) = k7_lattices(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2130,c_739,c_546,c_530,c_527,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.56/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.97  
% 2.56/0.97  ------  iProver source info
% 2.56/0.97  
% 2.56/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.97  git: non_committed_changes: false
% 2.56/0.97  git: last_make_outside_of_git: false
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.97  --sat_gr_def                            false
% 2.56/0.97  --sat_epr_types                         true
% 2.56/0.97  --sat_non_cyclic_types                  false
% 2.56/0.97  --sat_finite_models                     false
% 2.56/0.97  --sat_fm_lemmas                         false
% 2.56/0.97  --sat_fm_prep                           false
% 2.56/0.97  --sat_fm_uc_incr                        true
% 2.56/0.97  --sat_out_model                         small
% 2.56/0.97  --sat_out_clauses                       false
% 2.56/0.97  
% 2.56/0.97  ------ QBF Options
% 2.56/0.97  
% 2.56/0.97  --qbf_mode                              false
% 2.56/0.97  --qbf_elim_univ                         false
% 2.56/0.97  --qbf_dom_inst                          none
% 2.56/0.97  --qbf_dom_pre_inst                      false
% 2.56/0.97  --qbf_sk_in                             false
% 2.56/0.97  --qbf_pred_elim                         true
% 2.56/0.97  --qbf_split                             512
% 2.56/0.97  
% 2.56/0.97  ------ BMC1 Options
% 2.56/0.97  
% 2.56/0.97  --bmc1_incremental                      false
% 2.56/0.97  --bmc1_axioms                           reachable_all
% 2.56/0.97  --bmc1_min_bound                        0
% 2.56/0.97  --bmc1_max_bound                        -1
% 2.56/0.97  --bmc1_max_bound_default                -1
% 2.56/0.97  --bmc1_symbol_reachability              true
% 2.56/0.97  --bmc1_property_lemmas                  false
% 2.56/0.97  --bmc1_k_induction                      false
% 2.56/0.97  --bmc1_non_equiv_states                 false
% 2.56/0.97  --bmc1_deadlock                         false
% 2.56/0.97  --bmc1_ucm                              false
% 2.56/0.97  --bmc1_add_unsat_core                   none
% 2.56/0.97  --bmc1_unsat_core_children              false
% 2.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.97  --bmc1_out_stat                         full
% 2.56/0.97  --bmc1_ground_init                      false
% 2.56/0.97  --bmc1_pre_inst_next_state              false
% 2.56/0.97  --bmc1_pre_inst_state                   false
% 2.56/0.97  --bmc1_pre_inst_reach_state             false
% 2.56/0.97  --bmc1_out_unsat_core                   false
% 2.56/0.97  --bmc1_aig_witness_out                  false
% 2.56/0.97  --bmc1_verbose                          false
% 2.56/0.97  --bmc1_dump_clauses_tptp                false
% 2.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.97  --bmc1_dump_file                        -
% 2.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.97  --bmc1_ucm_extend_mode                  1
% 2.56/0.97  --bmc1_ucm_init_mode                    2
% 2.56/0.97  --bmc1_ucm_cone_mode                    none
% 2.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.97  --bmc1_ucm_relax_model                  4
% 2.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.97  --bmc1_ucm_layered_model                none
% 2.56/0.97  --bmc1_ucm_max_lemma_size               10
% 2.56/0.97  
% 2.56/0.97  ------ AIG Options
% 2.56/0.97  
% 2.56/0.97  --aig_mode                              false
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation Options
% 2.56/0.97  
% 2.56/0.97  --instantiation_flag                    true
% 2.56/0.97  --inst_sos_flag                         false
% 2.56/0.97  --inst_sos_phase                        true
% 2.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel_side                     num_symb
% 2.56/0.97  --inst_solver_per_active                1400
% 2.56/0.97  --inst_solver_calls_frac                1.
% 2.56/0.97  --inst_passive_queue_type               priority_queues
% 2.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.97  --inst_passive_queues_freq              [25;2]
% 2.56/0.97  --inst_dismatching                      true
% 2.56/0.97  --inst_eager_unprocessed_to_passive     true
% 2.56/0.97  --inst_prop_sim_given                   true
% 2.56/0.97  --inst_prop_sim_new                     false
% 2.56/0.97  --inst_subs_new                         false
% 2.56/0.97  --inst_eq_res_simp                      false
% 2.56/0.97  --inst_subs_given                       false
% 2.56/0.97  --inst_orphan_elimination               true
% 2.56/0.97  --inst_learning_loop_flag               true
% 2.56/0.97  --inst_learning_start                   3000
% 2.56/0.97  --inst_learning_factor                  2
% 2.56/0.97  --inst_start_prop_sim_after_learn       3
% 2.56/0.97  --inst_sel_renew                        solver
% 2.56/0.97  --inst_lit_activity_flag                true
% 2.56/0.97  --inst_restr_to_given                   false
% 2.56/0.97  --inst_activity_threshold               500
% 2.56/0.97  --inst_out_proof                        true
% 2.56/0.97  
% 2.56/0.97  ------ Resolution Options
% 2.56/0.97  
% 2.56/0.97  --resolution_flag                       true
% 2.56/0.97  --res_lit_sel                           adaptive
% 2.56/0.97  --res_lit_sel_side                      none
% 2.56/0.97  --res_ordering                          kbo
% 2.56/0.97  --res_to_prop_solver                    active
% 2.56/0.97  --res_prop_simpl_new                    false
% 2.56/0.97  --res_prop_simpl_given                  true
% 2.56/0.97  --res_passive_queue_type                priority_queues
% 2.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.97  --res_passive_queues_freq               [15;5]
% 2.56/0.97  --res_forward_subs                      full
% 2.56/0.97  --res_backward_subs                     full
% 2.56/0.97  --res_forward_subs_resolution           true
% 2.56/0.97  --res_backward_subs_resolution          true
% 2.56/0.97  --res_orphan_elimination                true
% 2.56/0.97  --res_time_limit                        2.
% 2.56/0.97  --res_out_proof                         true
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Options
% 2.56/0.97  
% 2.56/0.97  --superposition_flag                    true
% 2.56/0.97  --sup_passive_queue_type                priority_queues
% 2.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.97  --demod_completeness_check              fast
% 2.56/0.97  --demod_use_ground                      true
% 2.56/0.97  --sup_to_prop_solver                    passive
% 2.56/0.97  --sup_prop_simpl_new                    true
% 2.56/0.97  --sup_prop_simpl_given                  true
% 2.56/0.97  --sup_fun_splitting                     false
% 2.56/0.97  --sup_smt_interval                      50000
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Simplification Setup
% 2.56/0.97  
% 2.56/0.97  --sup_indices_passive                   []
% 2.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_full_bw                           [BwDemod]
% 2.56/0.97  --sup_immed_triv                        [TrivRules]
% 2.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_immed_bw_main                     []
% 2.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  
% 2.56/0.97  ------ Combination Options
% 2.56/0.97  
% 2.56/0.97  --comb_res_mult                         3
% 2.56/0.97  --comb_sup_mult                         2
% 2.56/0.97  --comb_inst_mult                        10
% 2.56/0.97  
% 2.56/0.97  ------ Debug Options
% 2.56/0.97  
% 2.56/0.97  --dbg_backtrace                         false
% 2.56/0.97  --dbg_dump_prop_clauses                 false
% 2.56/0.97  --dbg_dump_prop_clauses_file            -
% 2.56/0.97  --dbg_out_stat                          false
% 2.56/0.97  ------ Parsing...
% 2.56/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/0.97  ------ Proving...
% 2.56/0.97  ------ Problem Properties 
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  clauses                                 9
% 2.56/0.97  conjectures                             2
% 2.56/0.97  EPR                                     0
% 2.56/0.97  Horn                                    9
% 2.56/0.97  unary                                   2
% 2.56/0.97  binary                                  3
% 2.56/0.97  lits                                    21
% 2.56/0.97  lits eq                                 9
% 2.56/0.97  fd_pure                                 0
% 2.56/0.97  fd_pseudo                               0
% 2.56/0.97  fd_cond                                 0
% 2.56/0.97  fd_pseudo_cond                          0
% 2.56/0.97  AC symbols                              0
% 2.56/0.97  
% 2.56/0.97  ------ Schedule dynamic 5 is on 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  Current options:
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.97  --sat_gr_def                            false
% 2.56/0.97  --sat_epr_types                         true
% 2.56/0.97  --sat_non_cyclic_types                  false
% 2.56/0.97  --sat_finite_models                     false
% 2.56/0.97  --sat_fm_lemmas                         false
% 2.56/0.97  --sat_fm_prep                           false
% 2.56/0.97  --sat_fm_uc_incr                        true
% 2.56/0.97  --sat_out_model                         small
% 2.56/0.97  --sat_out_clauses                       false
% 2.56/0.97  
% 2.56/0.97  ------ QBF Options
% 2.56/0.97  
% 2.56/0.97  --qbf_mode                              false
% 2.56/0.97  --qbf_elim_univ                         false
% 2.56/0.97  --qbf_dom_inst                          none
% 2.56/0.97  --qbf_dom_pre_inst                      false
% 2.56/0.97  --qbf_sk_in                             false
% 2.56/0.97  --qbf_pred_elim                         true
% 2.56/0.97  --qbf_split                             512
% 2.56/0.97  
% 2.56/0.97  ------ BMC1 Options
% 2.56/0.97  
% 2.56/0.97  --bmc1_incremental                      false
% 2.56/0.97  --bmc1_axioms                           reachable_all
% 2.56/0.97  --bmc1_min_bound                        0
% 2.56/0.97  --bmc1_max_bound                        -1
% 2.56/0.97  --bmc1_max_bound_default                -1
% 2.56/0.97  --bmc1_symbol_reachability              true
% 2.56/0.97  --bmc1_property_lemmas                  false
% 2.56/0.97  --bmc1_k_induction                      false
% 2.56/0.97  --bmc1_non_equiv_states                 false
% 2.56/0.97  --bmc1_deadlock                         false
% 2.56/0.97  --bmc1_ucm                              false
% 2.56/0.97  --bmc1_add_unsat_core                   none
% 2.56/0.97  --bmc1_unsat_core_children              false
% 2.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.97  --bmc1_out_stat                         full
% 2.56/0.97  --bmc1_ground_init                      false
% 2.56/0.97  --bmc1_pre_inst_next_state              false
% 2.56/0.97  --bmc1_pre_inst_state                   false
% 2.56/0.97  --bmc1_pre_inst_reach_state             false
% 2.56/0.97  --bmc1_out_unsat_core                   false
% 2.56/0.97  --bmc1_aig_witness_out                  false
% 2.56/0.97  --bmc1_verbose                          false
% 2.56/0.97  --bmc1_dump_clauses_tptp                false
% 2.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.97  --bmc1_dump_file                        -
% 2.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.97  --bmc1_ucm_extend_mode                  1
% 2.56/0.97  --bmc1_ucm_init_mode                    2
% 2.56/0.97  --bmc1_ucm_cone_mode                    none
% 2.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.97  --bmc1_ucm_relax_model                  4
% 2.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.97  --bmc1_ucm_layered_model                none
% 2.56/0.97  --bmc1_ucm_max_lemma_size               10
% 2.56/0.97  
% 2.56/0.97  ------ AIG Options
% 2.56/0.97  
% 2.56/0.97  --aig_mode                              false
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation Options
% 2.56/0.97  
% 2.56/0.97  --instantiation_flag                    true
% 2.56/0.97  --inst_sos_flag                         false
% 2.56/0.97  --inst_sos_phase                        true
% 2.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel_side                     none
% 2.56/0.97  --inst_solver_per_active                1400
% 2.56/0.97  --inst_solver_calls_frac                1.
% 2.56/0.97  --inst_passive_queue_type               priority_queues
% 2.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.97  --inst_passive_queues_freq              [25;2]
% 2.56/0.97  --inst_dismatching                      true
% 2.56/0.97  --inst_eager_unprocessed_to_passive     true
% 2.56/0.97  --inst_prop_sim_given                   true
% 2.56/0.97  --inst_prop_sim_new                     false
% 2.56/0.97  --inst_subs_new                         false
% 2.56/0.97  --inst_eq_res_simp                      false
% 2.56/0.97  --inst_subs_given                       false
% 2.56/0.97  --inst_orphan_elimination               true
% 2.56/0.97  --inst_learning_loop_flag               true
% 2.56/0.97  --inst_learning_start                   3000
% 2.56/0.97  --inst_learning_factor                  2
% 2.56/0.97  --inst_start_prop_sim_after_learn       3
% 2.56/0.97  --inst_sel_renew                        solver
% 2.56/0.97  --inst_lit_activity_flag                true
% 2.56/0.97  --inst_restr_to_given                   false
% 2.56/0.97  --inst_activity_threshold               500
% 2.56/0.97  --inst_out_proof                        true
% 2.56/0.97  
% 2.56/0.97  ------ Resolution Options
% 2.56/0.97  
% 2.56/0.97  --resolution_flag                       false
% 2.56/0.97  --res_lit_sel                           adaptive
% 2.56/0.97  --res_lit_sel_side                      none
% 2.56/0.97  --res_ordering                          kbo
% 2.56/0.97  --res_to_prop_solver                    active
% 2.56/0.97  --res_prop_simpl_new                    false
% 2.56/0.97  --res_prop_simpl_given                  true
% 2.56/0.97  --res_passive_queue_type                priority_queues
% 2.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.97  --res_passive_queues_freq               [15;5]
% 2.56/0.97  --res_forward_subs                      full
% 2.56/0.97  --res_backward_subs                     full
% 2.56/0.97  --res_forward_subs_resolution           true
% 2.56/0.97  --res_backward_subs_resolution          true
% 2.56/0.97  --res_orphan_elimination                true
% 2.56/0.97  --res_time_limit                        2.
% 2.56/0.97  --res_out_proof                         true
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Options
% 2.56/0.97  
% 2.56/0.97  --superposition_flag                    true
% 2.56/0.97  --sup_passive_queue_type                priority_queues
% 2.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.97  --demod_completeness_check              fast
% 2.56/0.97  --demod_use_ground                      true
% 2.56/0.97  --sup_to_prop_solver                    passive
% 2.56/0.97  --sup_prop_simpl_new                    true
% 2.56/0.97  --sup_prop_simpl_given                  true
% 2.56/0.97  --sup_fun_splitting                     false
% 2.56/0.97  --sup_smt_interval                      50000
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Simplification Setup
% 2.56/0.97  
% 2.56/0.97  --sup_indices_passive                   []
% 2.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_full_bw                           [BwDemod]
% 2.56/0.97  --sup_immed_triv                        [TrivRules]
% 2.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_immed_bw_main                     []
% 2.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  
% 2.56/0.97  ------ Combination Options
% 2.56/0.97  
% 2.56/0.97  --comb_res_mult                         3
% 2.56/0.97  --comb_sup_mult                         2
% 2.56/0.97  --comb_inst_mult                        10
% 2.56/0.97  
% 2.56/0.97  ------ Debug Options
% 2.56/0.97  
% 2.56/0.97  --dbg_backtrace                         false
% 2.56/0.97  --dbg_dump_prop_clauses                 false
% 2.56/0.97  --dbg_dump_prop_clauses_file            -
% 2.56/0.97  --dbg_out_stat                          false
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  ------ Proving...
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  % SZS status Theorem for theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  fof(f8,conjecture,(
% 2.56/0.97    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f9,negated_conjecture,(
% 2.56/0.97    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.56/0.97    inference(negated_conjecture,[],[f8])).
% 2.56/0.97  
% 2.56/0.97  fof(f29,plain,(
% 2.56/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.56/0.97    inference(ennf_transformation,[],[f9])).
% 2.56/0.97  
% 2.56/0.97  fof(f30,plain,(
% 2.56/0.97    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.56/0.97    inference(flattening,[],[f29])).
% 2.56/0.97  
% 2.56/0.97  fof(f34,plain,(
% 2.56/0.97    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f33,plain,(
% 2.56/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1)) & r3_lattices(X0,sK1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f32,plain,(
% 2.56/0.97    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f35,plain,(
% 2.56/0.97    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).
% 2.56/0.97  
% 2.56/0.97  fof(f50,plain,(
% 2.56/0.97    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.56/0.97    inference(cnf_transformation,[],[f35])).
% 2.56/0.97  
% 2.56/0.97  fof(f49,plain,(
% 2.56/0.97    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.56/0.97    inference(cnf_transformation,[],[f35])).
% 2.56/0.97  
% 2.56/0.97  fof(f3,axiom,(
% 2.56/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f20,plain,(
% 2.56/0.97    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.56/0.97    inference(ennf_transformation,[],[f3])).
% 2.56/0.97  
% 2.56/0.97  fof(f21,plain,(
% 2.56/0.97    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.97    inference(flattening,[],[f20])).
% 2.56/0.97  
% 2.56/0.97  fof(f39,plain,(
% 2.56/0.97    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f21])).
% 2.56/0.97  
% 2.56/0.97  fof(f45,plain,(
% 2.56/0.97    ~v2_struct_0(sK0)),
% 2.56/0.97    inference(cnf_transformation,[],[f35])).
% 2.56/0.97  
% 2.56/0.97  fof(f48,plain,(
% 2.56/0.97    l3_lattices(sK0)),
% 2.56/0.97    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f6,axiom,(
% 2.56/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f25,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f6])).
% 2.56/0.98  
% 2.56/0.98  fof(f26,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f25])).
% 2.56/0.98  
% 2.56/0.98  fof(f42,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f26])).
% 2.56/0.98  
% 2.56/0.98  fof(f47,plain,(
% 2.56/0.98    v17_lattices(sK0)),
% 2.56/0.98    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f46,plain,(
% 2.56/0.98    v10_lattices(sK0)),
% 2.56/0.98    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f5,axiom,(
% 2.56/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f23,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f5])).
% 2.56/0.98  
% 2.56/0.98  fof(f24,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f23])).
% 2.56/0.98  
% 2.56/0.98  fof(f41,plain,(
% 2.56/0.98    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f24])).
% 2.56/0.98  
% 2.56/0.98  fof(f51,plain,(
% 2.56/0.98    r3_lattices(sK0,sK1,sK2)),
% 2.56/0.98    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f7,axiom,(
% 2.56/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f27,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f7])).
% 2.56/0.98  
% 2.56/0.98  fof(f28,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f27])).
% 2.56/0.98  
% 2.56/0.98  fof(f31,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (! [X2] : (((k4_lattices(X0,X1,X2) = k5_lattices(X0) | ~r3_lattices(X0,X1,k7_lattices(X0,X2))) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(nnf_transformation,[],[f28])).
% 2.56/0.98  
% 2.56/0.98  fof(f44,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k5_lattices(X0) | ~r3_lattices(X0,X1,k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f31])).
% 2.56/0.98  
% 2.56/0.98  fof(f1,axiom,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f11,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f1])).
% 2.56/0.98  
% 2.56/0.98  fof(f12,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f11])).
% 2.56/0.98  
% 2.56/0.98  fof(f13,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f12])).
% 2.56/0.98  
% 2.56/0.98  fof(f14,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f13])).
% 2.56/0.98  
% 2.56/0.98  fof(f15,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f14])).
% 2.56/0.98  
% 2.56/0.98  fof(f16,plain,(
% 2.56/0.98    ! [X0] : (((v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.56/0.98    inference(ennf_transformation,[],[f15])).
% 2.56/0.98  
% 2.56/0.98  fof(f17,plain,(
% 2.56/0.98    ! [X0] : ((v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.56/0.98    inference(flattening,[],[f16])).
% 2.56/0.98  
% 2.56/0.98  fof(f37,plain,(
% 2.56/0.98    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f17])).
% 2.56/0.98  
% 2.56/0.98  fof(f4,axiom,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f10,plain,(
% 2.56/0.98    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f4])).
% 2.56/0.98  
% 2.56/0.98  fof(f22,plain,(
% 2.56/0.98    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 2.56/0.98    inference(ennf_transformation,[],[f10])).
% 2.56/0.98  
% 2.56/0.98  fof(f40,plain,(
% 2.56/0.98    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f22])).
% 2.56/0.98  
% 2.56/0.98  fof(f2,axiom,(
% 2.56/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f18,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f2])).
% 2.56/0.98  
% 2.56/0.98  fof(f19,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f18])).
% 2.56/0.98  
% 2.56/0.98  fof(f38,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f19])).
% 2.56/0.98  
% 2.56/0.98  fof(f52,plain,(
% 2.56/0.98    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 2.56/0.98    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f43,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f31])).
% 2.56/0.98  
% 2.56/0.98  cnf(c_11,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_519,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_672,plain,
% 2.56/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_12,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_518,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_673,plain,
% 2.56/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1) ),
% 2.56/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_16,negated_conjecture,
% 2.56/0.98      ( ~ v2_struct_0(sK0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_368,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | sK0 != X1 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_369,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_368]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_13,negated_conjecture,
% 2.56/0.98      ( l3_lattices(sK0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_373,plain,
% 2.56/0.98      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_369,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_374,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 2.56/0.98      inference(renaming,[status(thm)],[c_373]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_514,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_374]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_677,plain,
% 2.56/0.98      ( m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top
% 2.56/0.98      | m1_subset_1(k7_lattices(sK0,X0_44),u1_struct_0(sK0)) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_6,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ v17_lattices(X1)
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X1)
% 2.56/0.98      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_14,negated_conjecture,
% 2.56/0.98      ( v17_lattices(sK0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_287,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X1)
% 2.56/0.98      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
% 2.56/0.98      | sK0 != X1 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_288,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0)
% 2.56/0.98      | v2_struct_0(sK0)
% 2.56/0.98      | ~ v10_lattices(sK0)
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_287]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_15,negated_conjecture,
% 2.56/0.98      ( v10_lattices(sK0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_292,plain,
% 2.56/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_288,c_16,c_15,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_293,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) = k7_lattices(sK0,k3_lattices(sK0,X1,X0)) ),
% 2.56/0.98      inference(renaming,[status(thm)],[c_292]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_517,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,X1_44),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,X1_44,X0_44)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_293]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_674,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,X0_44),k7_lattices(sK0,X1_44)) = k7_lattices(sK0,k3_lattices(sK0,X0_44,X1_44))
% 2.56/0.98      | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_922,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,X0_44)),k7_lattices(sK0,X1_44)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,X0_44),X1_44))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top
% 2.56/0.98      | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_677,c_674]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1982,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),X0_44))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_673,c_922]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_5,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ v17_lattices(X1)
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X1)
% 2.56/0.98      | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
% 2.56/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_308,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X1)
% 2.56/0.98      | k7_lattices(X1,k7_lattices(X1,X0)) = X0
% 2.56/0.98      | sK0 != X1 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_309,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0)
% 2.56/0.98      | v2_struct_0(sK0)
% 2.56/0.98      | ~ v10_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_308]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_313,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_309,c_16,c_15,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_516,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_313]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_675,plain,
% 2.56/0.98      ( k7_lattices(sK0,k7_lattices(sK0,X0_44)) = X0_44
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_782,plain,
% 2.56/0.98      ( k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_673,c_675]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1992,plain,
% 2.56/0.98      ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),X0_44)) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_44))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1982,c_782]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2119,plain,
% 2.56/0.98      ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_672,c_1992]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_781,plain,
% 2.56/0.98      ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_672,c_675]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_10,negated_conjecture,
% 2.56/0.98      ( r3_lattices(sK0,sK1,sK2) ),
% 2.56/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_7,plain,
% 2.56/0.98      ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/0.98      | ~ v17_lattices(X0)
% 2.56/0.98      | ~ l3_lattices(X0)
% 2.56/0.98      | v2_struct_0(X0)
% 2.56/0.98      | ~ v10_lattices(X0)
% 2.56/0.98      | k4_lattices(X0,X1,X2) = k5_lattices(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_263,plain,
% 2.56/0.98      ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/0.98      | ~ l3_lattices(X0)
% 2.56/0.98      | v2_struct_0(X0)
% 2.56/0.98      | ~ v10_lattices(X0)
% 2.56/0.98      | k4_lattices(X0,X1,X2) = k5_lattices(X0)
% 2.56/0.98      | sK0 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_264,plain,
% 2.56/0.98      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0)
% 2.56/0.98      | v2_struct_0(sK0)
% 2.56/0.98      | ~ v10_lattices(sK0)
% 2.56/0.98      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_263]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_268,plain,
% 2.56/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_264,c_16,c_15,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_269,plain,
% 2.56/0.98      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 2.56/0.98      inference(renaming,[status(thm)],[c_268]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_418,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,X1,X0) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0) != sK2
% 2.56/0.98      | sK1 != X1
% 2.56/0.98      | sK0 != sK0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_269]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_419,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,sK1,X0) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0) != sK2 ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_418]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_423,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,sK1,X0) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0) != sK2 ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_419,c_12]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_512,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,sK1,X0_44) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0_44) != sK2 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_423]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_679,plain,
% 2.56/0.98      ( k4_lattices(sK0,sK1,X0_44) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0_44) != sK2
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_858,plain,
% 2.56/0.98      ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
% 2.56/0.98      | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_781,c_679]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_739,plain,
% 2.56/0.98      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_514]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_742,plain,
% 2.56/0.98      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.56/0.98      | k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_516]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_743,plain,
% 2.56/0.98      ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,k7_lattices(sK0,sK2)) != sK2 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_512]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1441,plain,
% 2.56/0.98      ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_858,c_11,c_739,c_742,c_743]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_0,plain,
% 2.56/0.98      ( ~ l3_lattices(X0)
% 2.56/0.98      | v2_struct_0(X0)
% 2.56/0.98      | ~ v10_lattices(X0)
% 2.56/0.98      | v4_lattices(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_4,plain,
% 2.56/0.98      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l2_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v4_lattices(X1)
% 2.56/0.98      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_177,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X3)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v4_lattices(X1)
% 2.56/0.98      | X1 != X3
% 2.56/0.98      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_2]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_178,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v4_lattices(X1)
% 2.56/0.98      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_177]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_208,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X3)
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X3)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X3)
% 2.56/0.98      | X1 != X3
% 2.56/0.98      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_178]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_209,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | ~ v10_lattices(X1)
% 2.56/0.98      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_208]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_343,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.56/0.98      | ~ l3_lattices(X1)
% 2.56/0.98      | v2_struct_0(X1)
% 2.56/0.98      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 2.56/0.98      | sK0 != X1 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_209,c_15]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_344,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0)
% 2.56/0.98      | v2_struct_0(sK0)
% 2.56/0.98      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_343]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_348,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_344,c_16,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_349,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | k3_lattices(sK0,X1,X0) = k3_lattices(sK0,X0,X1) ),
% 2.56/0.98      inference(renaming,[status(thm)],[c_348]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_515,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1_44,u1_struct_0(sK0))
% 2.56/0.98      | k3_lattices(sK0,X1_44,X0_44) = k3_lattices(sK0,X0_44,X1_44) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_349]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_676,plain,
% 2.56/0.98      ( k3_lattices(sK0,X0_44,X1_44) = k3_lattices(sK0,X1_44,X0_44)
% 2.56/0.98      | m1_subset_1(X1_44,u1_struct_0(sK0)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1144,plain,
% 2.56/0.98      ( k3_lattices(sK0,X0_44,sK2) = k3_lattices(sK0,sK2,X0_44)
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_672,c_676]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1204,plain,
% 2.56/0.98      ( k3_lattices(sK0,k7_lattices(sK0,X0_44),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,X0_44))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_677,c_1144]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1448,plain,
% 2.56/0.98      ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_673,c_1204]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_920,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_44)) = k7_lattices(sK0,k3_lattices(sK0,sK2,X0_44))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_672,c_674]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_949,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,X0_44))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,X0_44)))
% 2.56/0.98      | m1_subset_1(X0_44,u1_struct_0(sK0)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_677,c_920]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1866,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_673,c_949]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1873,plain,
% 2.56/0.98      ( k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1866,c_782]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2130,plain,
% 2.56/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k5_lattices(sK0) ),
% 2.56/0.98      inference(light_normalisation,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_2119,c_1441,c_1448,c_1873]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_9,negated_conjecture,
% 2.56/0.98      ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_8,plain,
% 2.56/0.98      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/0.98      | ~ v17_lattices(X0)
% 2.56/0.98      | ~ l3_lattices(X0)
% 2.56/0.98      | v2_struct_0(X0)
% 2.56/0.98      | ~ v10_lattices(X0)
% 2.56/0.98      | k4_lattices(X0,X1,X2) != k5_lattices(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_239,plain,
% 2.56/0.98      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
% 2.56/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.56/0.98      | ~ l3_lattices(X0)
% 2.56/0.98      | v2_struct_0(X0)
% 2.56/0.98      | ~ v10_lattices(X0)
% 2.56/0.98      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
% 2.56/0.98      | sK0 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_240,plain,
% 2.56/0.98      ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ l3_lattices(sK0)
% 2.56/0.98      | v2_struct_0(sK0)
% 2.56/0.98      | ~ v10_lattices(sK0)
% 2.56/0.98      | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_239]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_244,plain,
% 2.56/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_240,c_16,c_15,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_245,plain,
% 2.56/0.98      ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
% 2.56/0.98      inference(renaming,[status(thm)],[c_244]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_400,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,X1,X0) != k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1)
% 2.56/0.98      | k7_lattices(sK0,sK2) != X1
% 2.56/0.98      | sK0 != sK0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_245]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_401,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK2),X0) != k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_400]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_513,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_44,u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_44) != k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,X0_44) != k7_lattices(sK0,sK1) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_401]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_546,plain,
% 2.56/0.98      ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.56/0.98      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.56/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0)
% 2.56/0.98      | k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_513]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_521,plain,( X0_44 = X0_44 ),theory(equality) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_530,plain,
% 2.56/0.98      ( sK1 = sK1 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_521]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_524,plain,
% 2.56/0.98      ( X0_44 != X1_44
% 2.56/0.98      | k7_lattices(X0_45,X0_44) = k7_lattices(X0_45,X1_44) ),
% 2.56/0.98      theory(equality) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_527,plain,
% 2.56/0.98      ( k7_lattices(sK0,sK1) = k7_lattices(sK0,sK1) | sK1 != sK1 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_524]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(contradiction,plain,
% 2.56/0.98      ( $false ),
% 2.56/0.98      inference(minisat,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_2130,c_739,c_546,c_530,c_527,c_11,c_12]) ).
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/0.98  
% 2.56/0.98  ------                               Statistics
% 2.56/0.98  
% 2.56/0.98  ------ General
% 2.56/0.98  
% 2.56/0.98  abstr_ref_over_cycles:                  0
% 2.56/0.98  abstr_ref_under_cycles:                 0
% 2.56/0.98  gc_basic_clause_elim:                   0
% 2.56/0.98  forced_gc_time:                         0
% 2.56/0.98  parsing_time:                           0.011
% 2.56/0.98  unif_index_cands_time:                  0.
% 2.56/0.98  unif_index_add_time:                    0.
% 2.56/0.98  orderings_time:                         0.
% 2.56/0.98  out_proof_time:                         0.01
% 2.56/0.98  total_time:                             0.103
% 2.56/0.98  num_of_symbols:                         47
% 2.56/0.98  num_of_terms:                           1464
% 2.56/0.98  
% 2.56/0.98  ------ Preprocessing
% 2.56/0.98  
% 2.56/0.98  num_of_splits:                          0
% 2.56/0.98  num_of_split_atoms:                     0
% 2.56/0.98  num_of_reused_defs:                     0
% 2.56/0.98  num_eq_ax_congr_red:                    17
% 2.56/0.98  num_of_sem_filtered_clauses:            1
% 2.56/0.98  num_of_subtypes:                        3
% 2.56/0.98  monotx_restored_types:                  0
% 2.56/0.98  sat_num_of_epr_types:                   0
% 2.56/0.98  sat_num_of_non_cyclic_types:            0
% 2.56/0.98  sat_guarded_non_collapsed_types:        1
% 2.56/0.98  num_pure_diseq_elim:                    0
% 2.56/0.98  simp_replaced_by:                       0
% 2.56/0.98  res_preprocessed:                       54
% 2.56/0.98  prep_upred:                             0
% 2.56/0.98  prep_unflattend:                        10
% 2.56/0.98  smt_new_axioms:                         0
% 2.56/0.98  pred_elim_cands:                        1
% 2.56/0.98  pred_elim:                              7
% 2.56/0.98  pred_elim_cl:                           7
% 2.56/0.98  pred_elim_cycles:                       9
% 2.56/0.98  merged_defs:                            0
% 2.56/0.98  merged_defs_ncl:                        0
% 2.56/0.98  bin_hyper_res:                          0
% 2.56/0.98  prep_cycles:                            4
% 2.56/0.98  pred_elim_time:                         0.006
% 2.56/0.98  splitting_time:                         0.
% 2.56/0.98  sem_filter_time:                        0.
% 2.56/0.98  monotx_time:                            0.
% 2.56/0.98  subtype_inf_time:                       0.
% 2.56/0.98  
% 2.56/0.98  ------ Problem properties
% 2.56/0.98  
% 2.56/0.98  clauses:                                9
% 2.56/0.98  conjectures:                            2
% 2.56/0.98  epr:                                    0
% 2.56/0.98  horn:                                   9
% 2.56/0.98  ground:                                 3
% 2.56/0.98  unary:                                  2
% 2.56/0.98  binary:                                 3
% 2.56/0.98  lits:                                   21
% 2.56/0.98  lits_eq:                                9
% 2.56/0.98  fd_pure:                                0
% 2.56/0.98  fd_pseudo:                              0
% 2.56/0.98  fd_cond:                                0
% 2.56/0.98  fd_pseudo_cond:                         0
% 2.56/0.98  ac_symbols:                             0
% 2.56/0.98  
% 2.56/0.98  ------ Propositional Solver
% 2.56/0.98  
% 2.56/0.98  prop_solver_calls:                      31
% 2.56/0.98  prop_fast_solver_calls:                 432
% 2.56/0.98  smt_solver_calls:                       0
% 2.56/0.98  smt_fast_solver_calls:                  0
% 2.56/0.98  prop_num_of_clauses:                    688
% 2.56/0.98  prop_preprocess_simplified:             2251
% 2.56/0.98  prop_fo_subsumed:                       19
% 2.56/0.98  prop_solver_time:                       0.
% 2.56/0.98  smt_solver_time:                        0.
% 2.56/0.98  smt_fast_solver_time:                   0.
% 2.56/0.98  prop_fast_solver_time:                  0.
% 2.56/0.98  prop_unsat_core_time:                   0.
% 2.56/0.98  
% 2.56/0.98  ------ QBF
% 2.56/0.98  
% 2.56/0.98  qbf_q_res:                              0
% 2.56/0.98  qbf_num_tautologies:                    0
% 2.56/0.98  qbf_prep_cycles:                        0
% 2.56/0.98  
% 2.56/0.98  ------ BMC1
% 2.56/0.98  
% 2.56/0.98  bmc1_current_bound:                     -1
% 2.56/0.98  bmc1_last_solved_bound:                 -1
% 2.56/0.98  bmc1_unsat_core_size:                   -1
% 2.56/0.98  bmc1_unsat_core_parents_size:           -1
% 2.56/0.98  bmc1_merge_next_fun:                    0
% 2.56/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.56/0.98  
% 2.56/0.98  ------ Instantiation
% 2.56/0.98  
% 2.56/0.98  inst_num_of_clauses:                    275
% 2.56/0.98  inst_num_in_passive:                    97
% 2.56/0.98  inst_num_in_active:                     174
% 2.56/0.98  inst_num_in_unprocessed:                4
% 2.56/0.98  inst_num_of_loops:                      190
% 2.56/0.98  inst_num_of_learning_restarts:          0
% 2.56/0.98  inst_num_moves_active_passive:          8
% 2.56/0.98  inst_lit_activity:                      0
% 2.56/0.98  inst_lit_activity_moves:                0
% 2.56/0.98  inst_num_tautologies:                   0
% 2.56/0.98  inst_num_prop_implied:                  0
% 2.56/0.98  inst_num_existing_simplified:           0
% 2.56/0.98  inst_num_eq_res_simplified:             0
% 2.56/0.98  inst_num_child_elim:                    0
% 2.56/0.98  inst_num_of_dismatching_blockings:      85
% 2.56/0.98  inst_num_of_non_proper_insts:           320
% 2.56/0.98  inst_num_of_duplicates:                 0
% 2.56/0.98  inst_inst_num_from_inst_to_res:         0
% 2.56/0.98  inst_dismatching_checking_time:         0.
% 2.56/0.98  
% 2.56/0.98  ------ Resolution
% 2.56/0.98  
% 2.56/0.98  res_num_of_clauses:                     0
% 2.56/0.98  res_num_in_passive:                     0
% 2.56/0.98  res_num_in_active:                      0
% 2.56/0.98  res_num_of_loops:                       58
% 2.56/0.98  res_forward_subset_subsumed:            59
% 2.56/0.98  res_backward_subset_subsumed:           0
% 2.56/0.98  res_forward_subsumed:                   0
% 2.56/0.98  res_backward_subsumed:                  0
% 2.56/0.98  res_forward_subsumption_resolution:     0
% 2.56/0.98  res_backward_subsumption_resolution:    0
% 2.56/0.98  res_clause_to_clause_subsumption:       155
% 2.56/0.98  res_orphan_elimination:                 0
% 2.56/0.98  res_tautology_del:                      55
% 2.56/0.98  res_num_eq_res_simplified:              1
% 2.56/0.98  res_num_sel_changes:                    0
% 2.56/0.98  res_moves_from_active_to_pass:          0
% 2.56/0.98  
% 2.56/0.98  ------ Superposition
% 2.56/0.98  
% 2.56/0.98  sup_time_total:                         0.
% 2.56/0.98  sup_time_generating:                    0.
% 2.56/0.98  sup_time_sim_full:                      0.
% 2.56/0.98  sup_time_sim_immed:                     0.
% 2.56/0.98  
% 2.56/0.98  sup_num_of_clauses:                     54
% 2.56/0.98  sup_num_in_active:                      37
% 2.56/0.98  sup_num_in_passive:                     17
% 2.56/0.98  sup_num_of_loops:                       37
% 2.56/0.98  sup_fw_superposition:                   53
% 2.56/0.98  sup_bw_superposition:                   5
% 2.56/0.98  sup_immediate_simplified:               18
% 2.56/0.98  sup_given_eliminated:                   0
% 2.56/0.98  comparisons_done:                       0
% 2.56/0.98  comparisons_avoided:                    0
% 2.56/0.98  
% 2.56/0.98  ------ Simplifications
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  sim_fw_subset_subsumed:                 2
% 2.56/0.98  sim_bw_subset_subsumed:                 0
% 2.56/0.98  sim_fw_subsumed:                        0
% 2.56/0.98  sim_bw_subsumed:                        0
% 2.56/0.98  sim_fw_subsumption_res:                 0
% 2.56/0.98  sim_bw_subsumption_res:                 0
% 2.56/0.98  sim_tautology_del:                      0
% 2.56/0.98  sim_eq_tautology_del:                   10
% 2.56/0.98  sim_eq_res_simp:                        0
% 2.56/0.98  sim_fw_demodulated:                     0
% 2.56/0.98  sim_bw_demodulated:                     1
% 2.56/0.98  sim_light_normalised:                   16
% 2.56/0.98  sim_joinable_taut:                      0
% 2.56/0.98  sim_joinable_simp:                      0
% 2.56/0.98  sim_ac_normalised:                      0
% 2.56/0.98  sim_smt_subsumption:                    0
% 2.56/0.98  
%------------------------------------------------------------------------------
