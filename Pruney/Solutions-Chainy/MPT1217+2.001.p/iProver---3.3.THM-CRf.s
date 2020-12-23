%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:22 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  188 (1412 expanded)
%              Number of clauses        :  123 ( 338 expanded)
%              Number of leaves         :   14 ( 424 expanded)
%              Depth                    :   24
%              Number of atoms          :  823 (9202 expanded)
%              Number of equality atoms :  145 ( 224 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f41,f40,f39])).

fof(f65,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_948,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1161,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_949,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1160,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_22,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_733,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_22])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_733])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_1166,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_333,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_334,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_75,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_336,plain,
    ( v4_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_25,c_24,c_22,c_75])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_336])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_9,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_59,plain,
    ( l2_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_25,c_22,c_59])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
    | k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_1164,plain,
    ( k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_2063,plain,
    ( k3_lattices(sK0,X0_50,k7_lattices(sK0,X1_50)) = k3_lattices(sK0,k7_lattices(sK0,X1_50),X0_50)
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1164])).

cnf(c_7998,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k3_lattices(sK0,k7_lattices(sK0,X1_50),k7_lattices(sK0,X0_50))
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_2063])).

cnf(c_17740,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_7998])).

cnf(c_17768,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1161,c_17740])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_25,c_24,c_22])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k4_lattices(sK0,X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_314])).

cnf(c_1162,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k4_lattices(sK0,X0_50,X1_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_1406,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1162])).

cnf(c_1434,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1161,c_1406])).

cnf(c_10,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_344,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_345,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_78,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_347,plain,
    ( v6_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_25,c_24,c_22,c_78])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_347])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_25,c_22])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
    | k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_1165,plain,
    ( k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_2776,plain,
    ( k2_lattices(sK0,sK1,X0_50) = k4_lattices(sK0,sK1,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1165])).

cnf(c_3080,plain,
    ( k2_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1160,c_2776])).

cnf(c_16,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_366,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_367,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | v9_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_84,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_369,plain,
    ( v9_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_25,c_24,c_22,c_84])).

cnf(c_622,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_369])).

cnf(c_623,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_81,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X0,X1)
    | k2_lattices(sK0,X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_25,c_24,c_22,c_81])).

cnf(c_628,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = X0 ),
    inference(renaming,[status(thm)],[c_627])).

cnf(c_19,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_495,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_347])).

cnf(c_496,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v9_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_25,c_24,c_22,c_81,c_84])).

cnf(c_501,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_602,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_501])).

cnf(c_603,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_605,plain,
    ( r1_lattices(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_21,c_20])).

cnf(c_829,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = X0
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_628,c_605])).

cnf(c_830,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k2_lattices(sK0,sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_832,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_21,c_20])).

cnf(c_937,plain,
    ( k2_lattices(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_832])).

cnf(c_3090,plain,
    ( k4_lattices(sK0,sK1,sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3080,c_937])).

cnf(c_1407,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k4_lattices(sK0,sK1,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1162])).

cnf(c_1807,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1160,c_1407])).

cnf(c_3283,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3090,c_1807])).

cnf(c_17775,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k7_lattices(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_17768,c_1434,c_3283])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_336])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_25,c_22,c_59])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
    | k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_390])).

cnf(c_1163,plain,
    ( k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_1508,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,X0_50),X1_50) = k3_lattices(sK0,k7_lattices(sK0,X0_50),X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1163])).

cnf(c_6564,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),X0_50) = k3_lattices(sK0,k7_lattices(sK0,sK2),X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1508])).

cnf(c_6729,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_6564])).

cnf(c_7247,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1161,c_6729])).

cnf(c_7254,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7247,c_1434])).

cnf(c_6,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_458,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_680,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_458,c_25])).

cnf(c_681,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_22])).

cnf(c_686,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(renaming,[status(thm)],[c_685])).

cnf(c_18,negated_conjecture,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_519,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_347])).

cnf(c_520,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v9_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_524,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_25,c_24,c_22,c_81,c_84])).

cnf(c_525,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_589,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != X1
    | k7_lattices(sK0,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_525])).

cnf(c_590,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1
    | k7_lattices(sK0,sK1) != X1
    | k7_lattices(sK0,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_686,c_590])).

cnf(c_796,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_940,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_796])).

cnf(c_1169,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_980,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1262,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_5916,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1169,c_21,c_20,c_980,c_940,c_1262])).

cnf(c_7376,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k7_lattices(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_7254,c_5916])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17775,c_7376])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.32/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.51  
% 7.32/1.51  ------  iProver source info
% 7.32/1.51  
% 7.32/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.51  git: non_committed_changes: false
% 7.32/1.51  git: last_make_outside_of_git: false
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     num_symb
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       true
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  ------ Parsing...
% 7.32/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.51  ------ Proving...
% 7.32/1.51  ------ Problem Properties 
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  clauses                                 14
% 7.32/1.51  conjectures                             2
% 7.32/1.51  EPR                                     0
% 7.32/1.51  Horn                                    14
% 7.32/1.51  unary                                   4
% 7.32/1.51  binary                                  2
% 7.32/1.51  lits                                    34
% 7.32/1.51  lits eq                                 14
% 7.32/1.51  fd_pure                                 0
% 7.32/1.51  fd_pseudo                               0
% 7.32/1.51  fd_cond                                 0
% 7.32/1.51  fd_pseudo_cond                          0
% 7.32/1.51  AC symbols                              0
% 7.32/1.51  
% 7.32/1.51  ------ Schedule dynamic 5 is on 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  Current options:
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     none
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       false
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ Proving...
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS status Theorem for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  fof(f11,conjecture,(
% 7.32/1.51    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f12,negated_conjecture,(
% 7.32/1.51    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 7.32/1.51    inference(negated_conjecture,[],[f11])).
% 7.32/1.51  
% 7.32/1.51  fof(f34,plain,(
% 7.32/1.51    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f12])).
% 7.32/1.51  
% 7.32/1.51  fof(f35,plain,(
% 7.32/1.51    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f34])).
% 7.32/1.51  
% 7.32/1.51  fof(f41,plain,(
% 7.32/1.51    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f40,plain,(
% 7.32/1.51    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1)) & r3_lattices(X0,sK1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f39,plain,(
% 7.32/1.51    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f42,plain,(
% 7.32/1.51    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f41,f40,f39])).
% 7.32/1.51  
% 7.32/1.51  fof(f65,plain,(
% 7.32/1.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f66,plain,(
% 7.32/1.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f4,axiom,(
% 7.32/1.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f21,plain,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f4])).
% 7.32/1.51  
% 7.32/1.51  fof(f22,plain,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f21])).
% 7.32/1.51  
% 7.32/1.51  fof(f51,plain,(
% 7.32/1.51    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f22])).
% 7.32/1.51  
% 7.32/1.51  fof(f61,plain,(
% 7.32/1.51    ~v2_struct_0(sK0)),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f64,plain,(
% 7.32/1.51    l3_lattices(sK0)),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f2,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f17,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f2])).
% 7.32/1.51  
% 7.32/1.51  fof(f18,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f17])).
% 7.32/1.51  
% 7.32/1.51  fof(f48,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f18])).
% 7.32/1.51  
% 7.32/1.51  fof(f1,axiom,(
% 7.32/1.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f13,plain,(
% 7.32/1.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.32/1.51    inference(pure_predicate_removal,[],[f1])).
% 7.32/1.51  
% 7.32/1.51  fof(f14,plain,(
% 7.32/1.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 7.32/1.51    inference(pure_predicate_removal,[],[f13])).
% 7.32/1.51  
% 7.32/1.51  fof(f15,plain,(
% 7.32/1.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 7.32/1.51    inference(ennf_transformation,[],[f14])).
% 7.32/1.51  
% 7.32/1.51  fof(f16,plain,(
% 7.32/1.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 7.32/1.51    inference(flattening,[],[f15])).
% 7.32/1.51  
% 7.32/1.51  fof(f44,plain,(
% 7.32/1.51    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f62,plain,(
% 7.32/1.51    v10_lattices(sK0)),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f5,axiom,(
% 7.32/1.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f23,plain,(
% 7.32/1.51    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 7.32/1.51    inference(ennf_transformation,[],[f5])).
% 7.32/1.51  
% 7.32/1.51  fof(f53,plain,(
% 7.32/1.51    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f23])).
% 7.32/1.51  
% 7.32/1.51  fof(f10,axiom,(
% 7.32/1.51    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f32,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f10])).
% 7.32/1.51  
% 7.32/1.51  fof(f33,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f32])).
% 7.32/1.51  
% 7.32/1.51  fof(f60,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f33])).
% 7.32/1.51  
% 7.32/1.51  fof(f63,plain,(
% 7.32/1.51    v17_lattices(sK0)),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f52,plain,(
% 7.32/1.51    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f23])).
% 7.32/1.51  
% 7.32/1.51  fof(f7,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f26,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f7])).
% 7.32/1.51  
% 7.32/1.51  fof(f27,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f26])).
% 7.32/1.51  
% 7.32/1.51  fof(f55,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f27])).
% 7.32/1.51  
% 7.32/1.51  fof(f45,plain,(
% 7.32/1.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f9,axiom,(
% 7.32/1.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f30,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f9])).
% 7.32/1.51  
% 7.32/1.51  fof(f31,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f30])).
% 7.32/1.51  
% 7.32/1.51  fof(f38,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(nnf_transformation,[],[f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f58,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f38])).
% 7.32/1.51  
% 7.32/1.51  fof(f47,plain,(
% 7.32/1.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f46,plain,(
% 7.32/1.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f67,plain,(
% 7.32/1.51    r3_lattices(sK0,sK1,sK2)),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f8,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f28,plain,(
% 7.32/1.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f8])).
% 7.32/1.51  
% 7.32/1.51  fof(f29,plain,(
% 7.32/1.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f28])).
% 7.32/1.51  
% 7.32/1.51  fof(f37,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(nnf_transformation,[],[f29])).
% 7.32/1.51  
% 7.32/1.51  fof(f56,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f37])).
% 7.32/1.51  
% 7.32/1.51  fof(f6,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f24,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f6])).
% 7.32/1.51  
% 7.32/1.51  fof(f25,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f24])).
% 7.32/1.51  
% 7.32/1.51  fof(f54,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f3,axiom,(
% 7.32/1.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f19,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f3])).
% 7.32/1.51  
% 7.32/1.51  fof(f20,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(flattening,[],[f19])).
% 7.32/1.51  
% 7.32/1.51  fof(f36,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 7.32/1.51    inference(nnf_transformation,[],[f20])).
% 7.32/1.51  
% 7.32/1.51  fof(f50,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  fof(f68,plain,(
% 7.32/1.51    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 7.32/1.51    inference(cnf_transformation,[],[f42])).
% 7.32/1.51  
% 7.32/1.51  fof(f57,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f37])).
% 7.32/1.51  
% 7.32/1.51  cnf(c_21,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_948,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_21]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1161,plain,
% 7.32/1.51      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_949,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_20]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1160,plain,
% 7.32/1.51      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_25,negated_conjecture,
% 7.32/1.51      ( ~ v2_struct_0(sK0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_728,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | sK0 != X1 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_729,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 7.32/1.51      | ~ l3_lattices(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_728]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_22,negated_conjecture,
% 7.32/1.51      ( l3_lattices(sK0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_733,plain,
% 7.32/1.51      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_729,c_22]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_734,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_733]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_943,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_734]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1166,plain,
% 7.32/1.51      ( m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l2_lattices(X1)
% 7.32/1.51      | ~ v4_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3,plain,
% 7.32/1.51      ( v4_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v10_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_24,negated_conjecture,
% 7.32/1.51      ( v10_lattices(sK0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_333,plain,
% 7.32/1.51      ( v4_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_334,plain,
% 7.32/1.51      ( v4_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_333]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_75,plain,
% 7.32/1.51      ( v4_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v10_lattices(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_336,plain,
% 7.32/1.51      ( v4_lattices(sK0) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_334,c_25,c_24,c_22,c_75]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_406,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l2_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 7.32/1.51      | sK0 != X1 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_5,c_336]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_407,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ l2_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_406]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9,plain,
% 7.32/1.51      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_59,plain,
% 7.32/1.51      ( l2_lattices(sK0) | ~ l3_lattices(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_411,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_407,c_25,c_22,c_59]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_945,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 7.32/1.51      | k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_411]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1164,plain,
% 7.32/1.51      ( k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2063,plain,
% 7.32/1.51      ( k3_lattices(sK0,X0_50,k7_lattices(sK0,X1_50)) = k3_lattices(sK0,k7_lattices(sK0,X1_50),X0_50)
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1166,c_1164]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7998,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k3_lattices(sK0,k7_lattices(sK0,X1_50),k7_lattices(sK0,X0_50))
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1166,c_2063]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17740,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1160,c_7998]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17768,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1161,c_17740]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ v17_lattices(X1)
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | ~ v10_lattices(X1)
% 7.32/1.51      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_23,negated_conjecture,
% 7.32/1.51      ( v17_lattices(sK0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_308,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | ~ v10_lattices(X1)
% 7.32/1.51      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
% 7.32/1.51      | sK0 != X1 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_309,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v10_lattices(sK0)
% 7.32/1.51      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_308]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_313,plain,
% 7.32/1.51      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_309,c_25,c_24,c_22]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_314,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_313]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_947,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 7.32/1.51      | k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k4_lattices(sK0,X0_50,X1_50)) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_314]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1162,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k4_lattices(sK0,X0_50,X1_50))
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1406,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0_50))
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1160,c_1162]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1434,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1161,c_1406]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10,plain,
% 7.32/1.51      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l1_lattices(X1)
% 7.32/1.51      | ~ v6_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_277,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ v6_lattices(X1)
% 7.32/1.51      | ~ l3_lattices(X3)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | X1 != X3
% 7.32/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_278,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ v6_lattices(X1)
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_277]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2,plain,
% 7.32/1.51      ( v6_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v10_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_344,plain,
% 7.32/1.51      ( v6_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_345,plain,
% 7.32/1.51      ( v6_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_344]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_78,plain,
% 7.32/1.51      ( v6_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v10_lattices(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_347,plain,
% 7.32/1.51      ( v6_lattices(sK0) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_345,c_25,c_24,c_22,c_78]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_543,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l3_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 7.32/1.51      | sK0 != X1 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_278,c_347]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_544,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_543]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_548,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_544,c_25,c_22]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_944,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 7.32/1.51      | k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_548]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1165,plain,
% 7.32/1.51      ( k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2776,plain,
% 7.32/1.51      ( k2_lattices(sK0,sK1,X0_50) = k4_lattices(sK0,sK1,X0_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1161,c_1165]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3080,plain,
% 7.32/1.51      ( k2_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK2) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1160,c_2776]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_16,plain,
% 7.32/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v9_lattices(X0)
% 7.32/1.51      | k2_lattices(X0,X1,X2) = X1 ),
% 7.32/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_0,plain,
% 7.32/1.51      ( ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v10_lattices(X0)
% 7.32/1.51      | v9_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_366,plain,
% 7.32/1.51      ( ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | v9_lattices(X0)
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_367,plain,
% 7.32/1.51      ( ~ l3_lattices(sK0) | v2_struct_0(sK0) | v9_lattices(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_366]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_84,plain,
% 7.32/1.51      ( ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v10_lattices(sK0)
% 7.32/1.51      | v9_lattices(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_369,plain,
% 7.32/1.51      ( v9_lattices(sK0) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_367,c_25,c_24,c_22,c_84]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_622,plain,
% 7.32/1.51      ( ~ r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | k2_lattices(X0,X1,X2) = X1
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_369]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_623,plain,
% 7.32/1.51      ( ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ v8_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = X0 ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_622]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1,plain,
% 7.32/1.51      ( v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v10_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_81,plain,
% 7.32/1.51      ( v8_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v10_lattices(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_627,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = X0 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_623,c_25,c_24,c_22,c_81]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_628,plain,
% 7.32/1.51      ( ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = X0 ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_627]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_19,negated_conjecture,
% 7.32/1.51      ( r3_lattices(sK0,sK1,sK2) ),
% 7.32/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_14,plain,
% 7.32/1.51      ( ~ r3_lattices(X0,X1,X2)
% 7.32/1.51      | r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v6_lattices(X0)
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v9_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_495,plain,
% 7.32/1.51      ( ~ r3_lattices(X0,X1,X2)
% 7.32/1.51      | r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v9_lattices(X0)
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_347]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_496,plain,
% 7.32/1.51      ( ~ r3_lattices(sK0,X0,X1)
% 7.32/1.51      | r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ v8_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v9_lattices(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_495]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_500,plain,
% 7.32/1.51      ( ~ r3_lattices(sK0,X0,X1)
% 7.32/1.51      | r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_496,c_25,c_24,c_22,c_81,c_84]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_501,plain,
% 7.32/1.51      ( ~ r3_lattices(sK0,X0,X1)
% 7.32/1.51      | r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_500]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_602,plain,
% 7.32/1.51      ( r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | sK1 != X0
% 7.32/1.51      | sK2 != X1
% 7.32/1.51      | sK0 != sK0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_19,c_501]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_603,plain,
% 7.32/1.51      ( r1_lattices(sK0,sK1,sK2)
% 7.32/1.51      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_602]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_605,plain,
% 7.32/1.51      ( r1_lattices(sK0,sK1,sK2) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_603,c_21,c_20]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_829,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k2_lattices(sK0,X0,X1) = X0
% 7.32/1.51      | sK1 != X0
% 7.32/1.51      | sK2 != X1
% 7.32/1.51      | sK0 != sK0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_628,c_605]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_830,plain,
% 7.32/1.51      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 7.32/1.51      | k2_lattices(sK0,sK1,sK2) = sK1 ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_829]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_832,plain,
% 7.32/1.51      ( k2_lattices(sK0,sK1,sK2) = sK1 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_830,c_21,c_20]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_937,plain,
% 7.32/1.51      ( k2_lattices(sK0,sK1,sK2) = sK1 ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_832]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3090,plain,
% 7.32/1.51      ( k4_lattices(sK0,sK1,sK2) = sK1 ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_3080,c_937]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1407,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k4_lattices(sK0,sK1,X0_50))
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1161,c_1162]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1807,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1160,c_1407]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3283,plain,
% 7.32/1.51      ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_3090,c_1807]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17775,plain,
% 7.32/1.51      ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(light_normalisation,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_17768,c_1434,c_3283]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l2_lattices(X1)
% 7.32/1.51      | ~ v4_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_385,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.32/1.51      | ~ l2_lattices(X1)
% 7.32/1.51      | v2_struct_0(X1)
% 7.32/1.51      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 7.32/1.51      | sK0 != X1 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_336]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_386,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ l2_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_385]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_390,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_386,c_25,c_22,c_59]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_946,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_390]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1163,plain,
% 7.32/1.51      ( k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1508,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,X0_50),X1_50) = k3_lattices(sK0,k7_lattices(sK0,X0_50),X1_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1166,c_1163]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_6564,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),X0_50) = k3_lattices(sK0,k7_lattices(sK0,sK2),X0_50)
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1160,c_1508]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_6729,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
% 7.32/1.51      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1166,c_6564]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7247,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1161,c_6729]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7254,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_7247,c_1434]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_6,plain,
% 7.32/1.51      ( r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ l2_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | k1_lattices(X0,X1,X2) != X2 ),
% 7.32/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_458,plain,
% 7.32/1.51      ( r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | k1_lattices(X0,X1,X2) != X2 ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_680,plain,
% 7.32/1.51      ( r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | k1_lattices(X0,X1,X2) != X2
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_458,c_25]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_681,plain,
% 7.32/1.51      ( r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | k1_lattices(sK0,X0,X1) != X1 ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_680]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_685,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | r1_lattices(sK0,X0,X1)
% 7.32/1.51      | k1_lattices(sK0,X0,X1) != X1 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_681,c_22]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_686,plain,
% 7.32/1.51      ( r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,X0,X1) != X1 ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_685]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18,negated_conjecture,
% 7.32/1.51      ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_13,plain,
% 7.32/1.51      ( r3_lattices(X0,X1,X2)
% 7.32/1.51      | ~ r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v6_lattices(X0)
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v9_lattices(X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_519,plain,
% 7.32/1.51      ( r3_lattices(X0,X1,X2)
% 7.32/1.51      | ~ r1_lattices(X0,X1,X2)
% 7.32/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.32/1.51      | ~ v8_lattices(X0)
% 7.32/1.51      | ~ l3_lattices(X0)
% 7.32/1.51      | v2_struct_0(X0)
% 7.32/1.51      | ~ v9_lattices(X0)
% 7.32/1.51      | sK0 != X0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_347]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_520,plain,
% 7.32/1.51      ( r3_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ v8_lattices(sK0)
% 7.32/1.51      | ~ l3_lattices(sK0)
% 7.32/1.51      | v2_struct_0(sK0)
% 7.32/1.51      | ~ v9_lattices(sK0) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_519]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_524,plain,
% 7.32/1.51      ( r3_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_520,c_25,c_24,c_22,c_81,c_84]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_525,plain,
% 7.32/1.51      ( r3_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_524]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_589,plain,
% 7.32/1.51      ( ~ r1_lattices(sK0,X0,X1)
% 7.32/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | k7_lattices(sK0,sK1) != X1
% 7.32/1.51      | k7_lattices(sK0,sK2) != X0
% 7.32/1.51      | sK0 != sK0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_525]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_590,plain,
% 7.32/1.51      ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_589]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_795,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,X0,X1) != X1
% 7.32/1.51      | k7_lattices(sK0,sK1) != X1
% 7.32/1.51      | k7_lattices(sK0,sK2) != X0
% 7.32/1.51      | sK0 != sK0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_686,c_590]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_796,plain,
% 7.32/1.51      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_795]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_940,plain,
% 7.32/1.51      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_796]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1169,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1)
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 7.32/1.51      | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_980,plain,
% 7.32/1.51      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_943]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1262,plain,
% 7.32/1.51      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_943]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5916,plain,
% 7.32/1.51      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_1169,c_21,c_20,c_980,c_940,c_1262]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7376,plain,
% 7.32/1.51      ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k7_lattices(sK0,sK1) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_7254,c_5916]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(contradiction,plain,
% 7.32/1.51      ( $false ),
% 7.32/1.51      inference(minisat,[status(thm)],[c_17775,c_7376]) ).
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  ------                               Statistics
% 7.32/1.51  
% 7.32/1.51  ------ General
% 7.32/1.51  
% 7.32/1.51  abstr_ref_over_cycles:                  0
% 7.32/1.51  abstr_ref_under_cycles:                 0
% 7.32/1.51  gc_basic_clause_elim:                   0
% 7.32/1.51  forced_gc_time:                         0
% 7.32/1.51  parsing_time:                           0.013
% 7.32/1.51  unif_index_cands_time:                  0.
% 7.32/1.51  unif_index_add_time:                    0.
% 7.32/1.51  orderings_time:                         0.
% 7.32/1.51  out_proof_time:                         0.017
% 7.32/1.51  total_time:                             0.761
% 7.32/1.51  num_of_symbols:                         53
% 7.32/1.51  num_of_terms:                           14502
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing
% 7.32/1.51  
% 7.32/1.51  num_of_splits:                          0
% 7.32/1.51  num_of_split_atoms:                     0
% 7.32/1.51  num_of_reused_defs:                     0
% 7.32/1.51  num_eq_ax_congr_red:                    30
% 7.32/1.51  num_of_sem_filtered_clauses:            1
% 7.32/1.51  num_of_subtypes:                        3
% 7.32/1.51  monotx_restored_types:                  0
% 7.32/1.51  sat_num_of_epr_types:                   0
% 7.32/1.51  sat_num_of_non_cyclic_types:            0
% 7.32/1.51  sat_guarded_non_collapsed_types:        1
% 7.32/1.51  num_pure_diseq_elim:                    0
% 7.32/1.51  simp_replaced_by:                       0
% 7.32/1.51  res_preprocessed:                       82
% 7.32/1.51  prep_upred:                             0
% 7.32/1.51  prep_unflattend:                        28
% 7.32/1.51  smt_new_axioms:                         0
% 7.32/1.51  pred_elim_cands:                        1
% 7.32/1.51  pred_elim:                              12
% 7.32/1.51  pred_elim_cl:                           11
% 7.32/1.51  pred_elim_cycles:                       14
% 7.32/1.51  merged_defs:                            0
% 7.32/1.51  merged_defs_ncl:                        0
% 7.32/1.51  bin_hyper_res:                          0
% 7.32/1.51  prep_cycles:                            4
% 7.32/1.51  pred_elim_time:                         0.012
% 7.32/1.51  splitting_time:                         0.
% 7.32/1.51  sem_filter_time:                        0.
% 7.32/1.51  monotx_time:                            0.
% 7.32/1.51  subtype_inf_time:                       0.
% 7.32/1.51  
% 7.32/1.51  ------ Problem properties
% 7.32/1.51  
% 7.32/1.51  clauses:                                14
% 7.32/1.51  conjectures:                            2
% 7.32/1.51  epr:                                    0
% 7.32/1.51  horn:                                   14
% 7.32/1.51  ground:                                 7
% 7.32/1.51  unary:                                  4
% 7.32/1.51  binary:                                 2
% 7.32/1.51  lits:                                   34
% 7.32/1.51  lits_eq:                                14
% 7.32/1.51  fd_pure:                                0
% 7.32/1.51  fd_pseudo:                              0
% 7.32/1.51  fd_cond:                                0
% 7.32/1.51  fd_pseudo_cond:                         0
% 7.32/1.51  ac_symbols:                             0
% 7.32/1.51  
% 7.32/1.51  ------ Propositional Solver
% 7.32/1.51  
% 7.32/1.51  prop_solver_calls:                      31
% 7.32/1.51  prop_fast_solver_calls:                 1026
% 7.32/1.51  smt_solver_calls:                       0
% 7.32/1.51  smt_fast_solver_calls:                  0
% 7.32/1.51  prop_num_of_clauses:                    4784
% 7.32/1.51  prop_preprocess_simplified:             11901
% 7.32/1.51  prop_fo_subsumed:                       72
% 7.32/1.51  prop_solver_time:                       0.
% 7.32/1.51  smt_solver_time:                        0.
% 7.32/1.51  smt_fast_solver_time:                   0.
% 7.32/1.51  prop_fast_solver_time:                  0.
% 7.32/1.51  prop_unsat_core_time:                   0.
% 7.32/1.51  
% 7.32/1.51  ------ QBF
% 7.32/1.51  
% 7.32/1.51  qbf_q_res:                              0
% 7.32/1.51  qbf_num_tautologies:                    0
% 7.32/1.51  qbf_prep_cycles:                        0
% 7.32/1.51  
% 7.32/1.51  ------ BMC1
% 7.32/1.51  
% 7.32/1.51  bmc1_current_bound:                     -1
% 7.32/1.51  bmc1_last_solved_bound:                 -1
% 7.32/1.51  bmc1_unsat_core_size:                   -1
% 7.32/1.51  bmc1_unsat_core_parents_size:           -1
% 7.32/1.51  bmc1_merge_next_fun:                    0
% 7.32/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation
% 7.32/1.51  
% 7.32/1.51  inst_num_of_clauses:                    2454
% 7.32/1.51  inst_num_in_passive:                    757
% 7.32/1.51  inst_num_in_active:                     917
% 7.32/1.51  inst_num_in_unprocessed:                780
% 7.32/1.51  inst_num_of_loops:                      940
% 7.32/1.51  inst_num_of_learning_restarts:          0
% 7.32/1.51  inst_num_moves_active_passive:          18
% 7.32/1.51  inst_lit_activity:                      0
% 7.32/1.51  inst_lit_activity_moves:                0
% 7.32/1.51  inst_num_tautologies:                   0
% 7.32/1.51  inst_num_prop_implied:                  0
% 7.32/1.51  inst_num_existing_simplified:           0
% 7.32/1.51  inst_num_eq_res_simplified:             0
% 7.32/1.51  inst_num_child_elim:                    0
% 7.32/1.51  inst_num_of_dismatching_blockings:      3614
% 7.32/1.51  inst_num_of_non_proper_insts:           3838
% 7.32/1.51  inst_num_of_duplicates:                 0
% 7.32/1.51  inst_inst_num_from_inst_to_res:         0
% 7.32/1.51  inst_dismatching_checking_time:         0.
% 7.32/1.51  
% 7.32/1.51  ------ Resolution
% 7.32/1.51  
% 7.32/1.51  res_num_of_clauses:                     0
% 7.32/1.51  res_num_in_passive:                     0
% 7.32/1.51  res_num_in_active:                      0
% 7.32/1.51  res_num_of_loops:                       86
% 7.32/1.51  res_forward_subset_subsumed:            164
% 7.32/1.51  res_backward_subset_subsumed:           4
% 7.32/1.51  res_forward_subsumed:                   0
% 7.32/1.51  res_backward_subsumed:                  0
% 7.32/1.51  res_forward_subsumption_resolution:     0
% 7.32/1.51  res_backward_subsumption_resolution:    0
% 7.32/1.51  res_clause_to_clause_subsumption:       569
% 7.32/1.51  res_orphan_elimination:                 0
% 7.32/1.51  res_tautology_del:                      583
% 7.32/1.51  res_num_eq_res_simplified:              1
% 7.32/1.51  res_num_sel_changes:                    0
% 7.32/1.51  res_moves_from_active_to_pass:          0
% 7.32/1.51  
% 7.32/1.51  ------ Superposition
% 7.32/1.51  
% 7.32/1.51  sup_time_total:                         0.
% 7.32/1.51  sup_time_generating:                    0.
% 7.32/1.51  sup_time_sim_full:                      0.
% 7.32/1.51  sup_time_sim_immed:                     0.
% 7.32/1.51  
% 7.32/1.51  sup_num_of_clauses:                     251
% 7.32/1.51  sup_num_in_active:                      184
% 7.32/1.51  sup_num_in_passive:                     67
% 7.32/1.51  sup_num_of_loops:                       187
% 7.32/1.51  sup_fw_superposition:                   199
% 7.32/1.51  sup_bw_superposition:                   48
% 7.32/1.51  sup_immediate_simplified:               58
% 7.32/1.51  sup_given_eliminated:                   0
% 7.32/1.51  comparisons_done:                       0
% 7.32/1.51  comparisons_avoided:                    0
% 7.32/1.51  
% 7.32/1.51  ------ Simplifications
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  sim_fw_subset_subsumed:                 4
% 7.32/1.51  sim_bw_subset_subsumed:                 0
% 7.32/1.51  sim_fw_subsumed:                        0
% 7.32/1.51  sim_bw_subsumed:                        0
% 7.32/1.51  sim_fw_subsumption_res:                 0
% 7.32/1.51  sim_bw_subsumption_res:                 0
% 7.32/1.51  sim_tautology_del:                      0
% 7.32/1.51  sim_eq_tautology_del:                   3
% 7.32/1.51  sim_eq_res_simp:                        0
% 7.32/1.51  sim_fw_demodulated:                     36
% 7.32/1.51  sim_bw_demodulated:                     4
% 7.32/1.51  sim_light_normalised:                   25
% 7.32/1.51  sim_joinable_taut:                      0
% 7.32/1.51  sim_joinable_simp:                      0
% 7.32/1.51  sim_ac_normalised:                      0
% 7.32/1.51  sim_smt_subsumption:                    0
% 7.32/1.51  
%------------------------------------------------------------------------------
