%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:22 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  181 (1027 expanded)
%              Number of clauses        :  116 ( 240 expanded)
%              Number of leaves         :   14 ( 309 expanded)
%              Depth                    :   25
%              Number of atoms          :  809 (6714 expanded)
%              Number of equality atoms :  131 ( 145 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_949,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1160,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

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

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f62])).

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

cnf(c_2787,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,X0_50),X1_50) = k4_lattices(sK0,k7_lattices(sK0,X0_50),X1_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1165])).

cnf(c_8985,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),X0_50) = k4_lattices(sK0,k7_lattices(sK0,sK2),X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_2787])).

cnf(c_9168,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_8985])).

cnf(c_9843,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1161,c_9168])).

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

cnf(c_2046,plain,
    ( k3_lattices(sK0,X0_50,sK2) = k3_lattices(sK0,sK2,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1164])).

cnf(c_2167,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1161,c_2046])).

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

cnf(c_1507,plain,
    ( k1_lattices(sK0,sK1,X0_50) = k3_lattices(sK0,sK1,X0_50)
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1163])).

cnf(c_1749,plain,
    ( k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1160,c_1507])).

cnf(c_7,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_435,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_704,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_435,c_25])).

cnf(c_705,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_22])).

cnf(c_710,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_709])).

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

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_84,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

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

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_710,c_605])).

cnf(c_822,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_824,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_21,c_20])).

cnf(c_938,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_824])).

cnf(c_1759,plain,
    ( k3_lattices(sK0,sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1749,c_938])).

cnf(c_2174,plain,
    ( k3_lattices(sK0,sK2,sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2167,c_1759])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
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
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_25,c_24,c_22])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k3_lattices(sK0,X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_314])).

cnf(c_1162,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k3_lattices(sK0,X0_50,X1_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_1406,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k3_lattices(sK0,sK2,X0_50))
    | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1162])).

cnf(c_1434,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1161,c_1406])).

cnf(c_2235,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_2174,c_1434])).

cnf(c_9850,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_9843,c_2235])).

cnf(c_1262,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_15,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0)
    | k2_lattices(X0,X1,X2) != X1 ),
    inference(cnf_transformation,[],[f59])).

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

cnf(c_369,plain,
    ( v9_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_25,c_24,c_22,c_84])).

cnf(c_646,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_369])).

cnf(c_647,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,X0,X1) != X0 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattices(sK0,X0,X1)
    | k2_lattices(sK0,X0,X1) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_25,c_24,c_22,c_81])).

cnf(c_652,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) != X0 ),
    inference(renaming,[status(thm)],[c_651])).

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

cnf(c_808,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) != X0
    | k7_lattices(sK0,sK1) != X1
    | k7_lattices(sK0,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_590])).

cnf(c_809,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_939,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_980,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9850,c_1262,c_939,c_980,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     num_symb
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       true
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 14
% 3.65/0.99  conjectures                             2
% 3.65/0.99  EPR                                     0
% 3.65/0.99  Horn                                    14
% 3.65/0.99  unary                                   4
% 3.65/0.99  binary                                  2
% 3.65/0.99  lits                                    34
% 3.65/0.99  lits eq                                 14
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 0
% 3.65/0.99  fd_pseudo_cond                          0
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Schedule dynamic 5 is on 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    --mode clausify
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         false
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     none
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       false
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     false
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   []
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_full_bw                           [BwDemod]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f11,conjecture,(
% 3.65/0.99    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f12,negated_conjecture,(
% 3.65/0.99    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 3.65/0.99    inference(negated_conjecture,[],[f11])).
% 3.65/0.99  
% 3.65/0.99  fof(f34,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f12])).
% 3.65/0.99  
% 3.65/0.99  fof(f35,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f34])).
% 3.65/0.99  
% 3.65/0.99  fof(f41,plain,(
% 3.65/0.99    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f40,plain,(
% 3.65/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1)) & r3_lattices(X0,sK1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f39,plain,(
% 3.65/0.99    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f42,plain,(
% 3.65/0.99    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f41,f40,f39])).
% 3.65/0.99  
% 3.65/0.99  fof(f65,plain,(
% 3.65/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f4,axiom,(
% 3.65/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f21,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f4])).
% 3.65/0.99  
% 3.65/0.99  fof(f22,plain,(
% 3.65/0.99    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f21])).
% 3.65/0.99  
% 3.65/0.99  fof(f51,plain,(
% 3.65/0.99    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f22])).
% 3.65/0.99  
% 3.65/0.99  fof(f61,plain,(
% 3.65/0.99    ~v2_struct_0(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f64,plain,(
% 3.65/0.99    l3_lattices(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f66,plain,(
% 3.65/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f5,axiom,(
% 3.65/0.99    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f23,plain,(
% 3.65/0.99    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f5])).
% 3.65/0.99  
% 3.65/0.99  fof(f52,plain,(
% 3.65/0.99    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f23])).
% 3.65/0.99  
% 3.65/0.99  fof(f7,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f26,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f7])).
% 3.65/0.99  
% 3.65/0.99  fof(f27,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f26])).
% 3.65/0.99  
% 3.65/0.99  fof(f55,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f27])).
% 3.65/0.99  
% 3.65/0.99  fof(f1,axiom,(
% 3.65/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f13,plain,(
% 3.65/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.65/0.99    inference(pure_predicate_removal,[],[f1])).
% 3.65/0.99  
% 3.65/0.99  fof(f14,plain,(
% 3.65/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.65/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.65/0.99  
% 3.65/0.99  fof(f15,plain,(
% 3.65/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f14])).
% 3.65/0.99  
% 3.65/0.99  fof(f16,plain,(
% 3.65/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.65/0.99    inference(flattening,[],[f15])).
% 3.65/0.99  
% 3.65/0.99  fof(f45,plain,(
% 3.65/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f62,plain,(
% 3.65/0.99    v10_lattices(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f2,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f17,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f2])).
% 3.65/0.99  
% 3.65/0.99  fof(f18,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f17])).
% 3.65/0.99  
% 3.65/0.99  fof(f48,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f44,plain,(
% 3.65/0.99    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f53,plain,(
% 3.65/0.99    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f23])).
% 3.65/0.99  
% 3.65/0.99  fof(f6,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f24,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f6])).
% 3.65/0.99  
% 3.65/0.99  fof(f25,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f24])).
% 3.65/0.99  
% 3.65/0.99  fof(f54,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f25])).
% 3.65/0.99  
% 3.65/0.99  fof(f3,axiom,(
% 3.65/0.99    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f19,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f3])).
% 3.65/0.99  
% 3.65/0.99  fof(f20,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f36,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(nnf_transformation,[],[f20])).
% 3.65/0.99  
% 3.65/0.99  fof(f49,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f36])).
% 3.65/0.99  
% 3.65/0.99  fof(f67,plain,(
% 3.65/0.99    r3_lattices(sK0,sK1,sK2)),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f8,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f28,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f8])).
% 3.65/0.99  
% 3.65/0.99  fof(f29,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f28])).
% 3.65/0.99  
% 3.65/0.99  fof(f37,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(nnf_transformation,[],[f29])).
% 3.65/0.99  
% 3.65/0.99  fof(f56,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f37])).
% 3.65/0.99  
% 3.65/0.99  fof(f46,plain,(
% 3.65/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f47,plain,(
% 3.65/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f10,axiom,(
% 3.65/0.99    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f32,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f10])).
% 3.65/0.99  
% 3.65/0.99  fof(f33,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f32])).
% 3.65/0.99  
% 3.65/0.99  fof(f60,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f33])).
% 3.65/0.99  
% 3.65/0.99  fof(f63,plain,(
% 3.65/0.99    v17_lattices(sK0)),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f9,axiom,(
% 3.65/0.99    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 3.65/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f30,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 3.65/0.99    inference(ennf_transformation,[],[f9])).
% 3.65/0.99  
% 3.65/0.99  fof(f31,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(flattening,[],[f30])).
% 3.65/0.99  
% 3.65/0.99  fof(f38,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.65/0.99    inference(nnf_transformation,[],[f31])).
% 3.65/0.99  
% 3.65/0.99  fof(f59,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f38])).
% 3.65/0.99  
% 3.65/0.99  fof(f68,plain,(
% 3.65/0.99    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 3.65/0.99    inference(cnf_transformation,[],[f42])).
% 3.65/0.99  
% 3.65/0.99  fof(f57,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f37])).
% 3.65/0.99  
% 3.65/0.99  cnf(c_21,negated_conjecture,
% 3.65/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_948,negated_conjecture,
% 3.65/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1161,plain,
% 3.65/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_8,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_25,negated_conjecture,
% 3.65/0.99      ( ~ v2_struct_0(sK0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_728,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | sK0 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_729,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 3.65/0.99      | ~ l3_lattices(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_728]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_22,negated_conjecture,
% 3.65/0.99      ( l3_lattices(sK0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_733,plain,
% 3.65/0.99      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_729,c_22]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_734,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_733]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_943,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 3.65/0.99      | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_734]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1166,plain,
% 3.65/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(k7_lattices(sK0,X0_50),u1_struct_0(sK0)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_20,negated_conjecture,
% 3.65/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_949,negated_conjecture,
% 3.65/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1160,plain,
% 3.65/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_10,plain,
% 3.65/0.99      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l1_lattices(X1)
% 3.65/0.99      | ~ v6_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_277,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ v6_lattices(X1)
% 3.65/0.99      | ~ l3_lattices(X3)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | X1 != X3
% 3.65/0.99      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_278,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ v6_lattices(X1)
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_277]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2,plain,
% 3.65/0.99      ( v6_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v10_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_24,negated_conjecture,
% 3.65/0.99      ( v10_lattices(sK0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_344,plain,
% 3.65/0.99      ( v6_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_345,plain,
% 3.65/0.99      ( v6_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_78,plain,
% 3.65/0.99      ( v6_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v10_lattices(sK0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_347,plain,
% 3.65/0.99      ( v6_lattices(sK0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_345,c_25,c_24,c_22,c_78]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_543,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 3.65/0.99      | sK0 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_278,c_347]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_544,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_548,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_544,c_25,c_22]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_944,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_548]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1165,plain,
% 3.65/0.99      ( k2_lattices(sK0,X0_50,X1_50) = k4_lattices(sK0,X0_50,X1_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2787,plain,
% 3.65/0.99      ( k2_lattices(sK0,k7_lattices(sK0,X0_50),X1_50) = k4_lattices(sK0,k7_lattices(sK0,X0_50),X1_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1166,c_1165]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_8985,plain,
% 3.65/0.99      ( k2_lattices(sK0,k7_lattices(sK0,sK2),X0_50) = k4_lattices(sK0,k7_lattices(sK0,sK2),X0_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1160,c_2787]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9168,plain,
% 3.65/0.99      ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50))
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1166,c_8985]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9843,plain,
% 3.65/0.99      ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1161,c_9168]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l2_lattices(X1)
% 3.65/0.99      | ~ v4_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3,plain,
% 3.65/0.99      ( v4_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v10_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_333,plain,
% 3.65/0.99      ( v4_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_334,plain,
% 3.65/0.99      ( v4_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_333]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_75,plain,
% 3.65/0.99      ( v4_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v10_lattices(sK0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_336,plain,
% 3.65/0.99      ( v4_lattices(sK0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_334,c_25,c_24,c_22,c_75]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_406,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l2_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 3.65/0.99      | sK0 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_336]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_407,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ l2_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9,plain,
% 3.65/0.99      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_59,plain,
% 3.65/0.99      ( l2_lattices(sK0) | ~ l3_lattices(sK0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_411,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_407,c_25,c_22,c_59]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_945,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 3.65/0.99      | k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_411]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1164,plain,
% 3.65/0.99      ( k3_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X1_50,X0_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2046,plain,
% 3.65/0.99      ( k3_lattices(sK0,X0_50,sK2) = k3_lattices(sK0,sK2,X0_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1160,c_1164]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2167,plain,
% 3.65/0.99      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1161,c_2046]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_11,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l2_lattices(X1)
% 3.65/0.99      | ~ v4_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_385,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l2_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 3.65/0.99      | sK0 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_336]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_386,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ l2_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_390,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = k3_lattices(sK0,X0,X1) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_386,c_25,c_22,c_59]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_946,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 3.65/0.99      | k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_390]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1163,plain,
% 3.65/0.99      ( k1_lattices(sK0,X0_50,X1_50) = k3_lattices(sK0,X0_50,X1_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1507,plain,
% 3.65/0.99      ( k1_lattices(sK0,sK1,X0_50) = k3_lattices(sK0,sK1,X0_50)
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1161,c_1163]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1749,plain,
% 3.65/0.99      ( k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1160,c_1507]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7,plain,
% 3.65/0.99      ( ~ r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ l2_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | k1_lattices(X0,X1,X2) = X2 ),
% 3.65/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_435,plain,
% 3.65/0.99      ( ~ r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | k1_lattices(X0,X1,X2) = X2 ),
% 3.65/0.99      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_704,plain,
% 3.65/0.99      ( ~ r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | k1_lattices(X0,X1,X2) = X2
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_435,c_25]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_705,plain,
% 3.65/0.99      ( ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = X1 ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_704]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_709,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = X1 ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_705,c_22]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_710,plain,
% 3.65/0.99      ( ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = X1 ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_709]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_19,negated_conjecture,
% 3.65/0.99      ( r3_lattices(sK0,sK1,sK2) ),
% 3.65/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14,plain,
% 3.65/0.99      ( ~ r3_lattices(X0,X1,X2)
% 3.65/0.99      | r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v6_lattices(X0)
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v9_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_495,plain,
% 3.65/0.99      ( ~ r3_lattices(X0,X1,X2)
% 3.65/0.99      | r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v9_lattices(X0)
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_347]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_496,plain,
% 3.65/0.99      ( ~ r3_lattices(sK0,X0,X1)
% 3.65/0.99      | r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ v8_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v9_lattices(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_495]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1,plain,
% 3.65/0.99      ( v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v10_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_81,plain,
% 3.65/0.99      ( v8_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v10_lattices(sK0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_0,plain,
% 3.65/0.99      ( ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v10_lattices(X0)
% 3.65/0.99      | v9_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_84,plain,
% 3.65/0.99      ( ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v10_lattices(sK0)
% 3.65/0.99      | v9_lattices(sK0) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_500,plain,
% 3.65/0.99      ( ~ r3_lattices(sK0,X0,X1)
% 3.65/0.99      | r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_496,c_25,c_24,c_22,c_81,c_84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_501,plain,
% 3.65/0.99      ( ~ r3_lattices(sK0,X0,X1)
% 3.65/0.99      | r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_500]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_602,plain,
% 3.65/0.99      ( r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | sK1 != X0
% 3.65/0.99      | sK2 != X1
% 3.65/0.99      | sK0 != sK0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_501]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_603,plain,
% 3.65/0.99      ( r1_lattices(sK0,sK1,sK2)
% 3.65/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_602]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_605,plain,
% 3.65/0.99      ( r1_lattices(sK0,sK1,sK2) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_603,c_21,c_20]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_821,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k1_lattices(sK0,X0,X1) = X1
% 3.65/0.99      | sK1 != X0
% 3.65/0.99      | sK2 != X1
% 3.65/0.99      | sK0 != sK0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_710,c_605]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_822,plain,
% 3.65/0.99      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 3.65/0.99      | k1_lattices(sK0,sK1,sK2) = sK2 ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_821]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_824,plain,
% 3.65/0.99      ( k1_lattices(sK0,sK1,sK2) = sK2 ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_822,c_21,c_20]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_938,plain,
% 3.65/0.99      ( k1_lattices(sK0,sK1,sK2) = sK2 ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_824]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1759,plain,
% 3.65/0.99      ( k3_lattices(sK0,sK1,sK2) = sK2 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_1749,c_938]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2174,plain,
% 3.65/0.99      ( k3_lattices(sK0,sK2,sK1) = sK2 ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_2167,c_1759]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_17,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ v17_lattices(X1)
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v10_lattices(X1)
% 3.65/0.99      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_23,negated_conjecture,
% 3.65/0.99      ( v17_lattices(sK0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_308,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.99      | ~ l3_lattices(X1)
% 3.65/0.99      | v2_struct_0(X1)
% 3.65/0.99      | ~ v10_lattices(X1)
% 3.65/0.99      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
% 3.65/0.99      | sK0 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_309,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v10_lattices(sK0)
% 3.65/0.99      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_313,plain,
% 3.65/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_309,c_25,c_24,c_22]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_314,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_313]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_947,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0_50,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(sK0))
% 3.65/0.99      | k4_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k3_lattices(sK0,X0_50,X1_50)) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_314]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1162,plain,
% 3.65/0.99      ( k4_lattices(sK0,k7_lattices(sK0,X0_50),k7_lattices(sK0,X1_50)) = k7_lattices(sK0,k3_lattices(sK0,X0_50,X1_50))
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top
% 3.65/0.99      | m1_subset_1(X1_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1406,plain,
% 3.65/0.99      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0_50)) = k7_lattices(sK0,k3_lattices(sK0,sK2,X0_50))
% 3.65/0.99      | m1_subset_1(X0_50,u1_struct_0(sK0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1160,c_1162]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1434,plain,
% 3.65/0.99      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1161,c_1406]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_2235,plain,
% 3.65/0.99      ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK2) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_2174,c_1434]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_9850,plain,
% 3.65/0.99      ( k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK2) ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_9843,c_2235]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1262,plain,
% 3.65/0.99      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_943]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_15,plain,
% 3.65/0.99      ( r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v9_lattices(X0)
% 3.65/0.99      | k2_lattices(X0,X1,X2) != X1 ),
% 3.65/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_366,plain,
% 3.65/0.99      ( ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | v9_lattices(X0)
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_367,plain,
% 3.65/0.99      ( ~ l3_lattices(sK0) | v2_struct_0(sK0) | v9_lattices(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_366]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_369,plain,
% 3.65/0.99      ( v9_lattices(sK0) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_367,c_25,c_24,c_22,c_84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_646,plain,
% 3.65/0.99      ( r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | k2_lattices(X0,X1,X2) != X1
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_369]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_647,plain,
% 3.65/0.99      ( r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ v8_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | k2_lattices(sK0,X0,X1) != X0 ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_646]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_651,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | r1_lattices(sK0,X0,X1)
% 3.65/0.99      | k2_lattices(sK0,X0,X1) != X0 ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_647,c_25,c_24,c_22,c_81]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_652,plain,
% 3.65/0.99      ( r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,X0,X1) != X0 ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_651]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_18,negated_conjecture,
% 3.65/0.99      ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13,plain,
% 3.65/0.99      ( r3_lattices(X0,X1,X2)
% 3.65/0.99      | ~ r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v6_lattices(X0)
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v9_lattices(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_519,plain,
% 3.65/0.99      ( r3_lattices(X0,X1,X2)
% 3.65/0.99      | ~ r1_lattices(X0,X1,X2)
% 3.65/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.99      | ~ v8_lattices(X0)
% 3.65/0.99      | ~ l3_lattices(X0)
% 3.65/0.99      | v2_struct_0(X0)
% 3.65/0.99      | ~ v9_lattices(X0)
% 3.65/0.99      | sK0 != X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_347]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_520,plain,
% 3.65/0.99      ( r3_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ v8_lattices(sK0)
% 3.65/0.99      | ~ l3_lattices(sK0)
% 3.65/0.99      | v2_struct_0(sK0)
% 3.65/0.99      | ~ v9_lattices(sK0) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_519]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_524,plain,
% 3.65/0.99      ( r3_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_520,c_25,c_24,c_22,c_81,c_84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_525,plain,
% 3.65/0.99      ( r3_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_524]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_589,plain,
% 3.65/0.99      ( ~ r1_lattices(sK0,X0,X1)
% 3.65/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | k7_lattices(sK0,sK1) != X1
% 3.65/0.99      | k7_lattices(sK0,sK2) != X0
% 3.65/0.99      | sK0 != sK0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_525]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_590,plain,
% 3.65/0.99      ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_808,plain,
% 3.65/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,X0,X1) != X0
% 3.65/0.99      | k7_lattices(sK0,sK1) != X1
% 3.65/0.99      | k7_lattices(sK0,sK2) != X0
% 3.65/0.99      | sK0 != sK0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_652,c_590]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_809,plain,
% 3.65/0.99      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK2) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_808]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_939,plain,
% 3.65/0.99      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.65/0.99      | k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK2) ),
% 3.65/0.99      inference(subtyping,[status(esa)],[c_809]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_980,plain,
% 3.65/0.99      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.65/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_943]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(contradiction,plain,
% 3.65/0.99      ( $false ),
% 3.65/0.99      inference(minisat,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_9850,c_1262,c_939,c_980,c_20,c_21]) ).
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  ------                               Statistics
% 3.65/0.99  
% 3.65/0.99  ------ General
% 3.65/0.99  
% 3.65/0.99  abstr_ref_over_cycles:                  0
% 3.65/0.99  abstr_ref_under_cycles:                 0
% 3.65/0.99  gc_basic_clause_elim:                   0
% 3.65/0.99  forced_gc_time:                         0
% 3.65/0.99  parsing_time:                           0.009
% 3.65/0.99  unif_index_cands_time:                  0.
% 3.65/0.99  unif_index_add_time:                    0.
% 3.65/0.99  orderings_time:                         0.
% 3.65/0.99  out_proof_time:                         0.01
% 3.65/0.99  total_time:                             0.314
% 3.65/0.99  num_of_symbols:                         53
% 3.65/0.99  num_of_terms:                           8657
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing
% 3.65/0.99  
% 3.65/0.99  num_of_splits:                          0
% 3.65/0.99  num_of_split_atoms:                     0
% 3.65/0.99  num_of_reused_defs:                     0
% 3.65/0.99  num_eq_ax_congr_red:                    30
% 3.65/0.99  num_of_sem_filtered_clauses:            1
% 3.65/0.99  num_of_subtypes:                        3
% 3.65/0.99  monotx_restored_types:                  0
% 3.65/0.99  sat_num_of_epr_types:                   0
% 3.65/0.99  sat_num_of_non_cyclic_types:            0
% 3.65/0.99  sat_guarded_non_collapsed_types:        1
% 3.65/0.99  num_pure_diseq_elim:                    0
% 3.65/0.99  simp_replaced_by:                       0
% 3.65/0.99  res_preprocessed:                       82
% 3.65/0.99  prep_upred:                             0
% 3.65/0.99  prep_unflattend:                        28
% 3.65/0.99  smt_new_axioms:                         0
% 3.65/0.99  pred_elim_cands:                        1
% 3.65/0.99  pred_elim:                              12
% 3.65/0.99  pred_elim_cl:                           11
% 3.65/0.99  pred_elim_cycles:                       14
% 3.65/0.99  merged_defs:                            0
% 3.65/0.99  merged_defs_ncl:                        0
% 3.65/0.99  bin_hyper_res:                          0
% 3.65/0.99  prep_cycles:                            4
% 3.65/0.99  pred_elim_time:                         0.011
% 3.65/0.99  splitting_time:                         0.
% 3.65/0.99  sem_filter_time:                        0.
% 3.65/0.99  monotx_time:                            0.
% 3.65/0.99  subtype_inf_time:                       0.
% 3.65/0.99  
% 3.65/0.99  ------ Problem properties
% 3.65/0.99  
% 3.65/0.99  clauses:                                14
% 3.65/0.99  conjectures:                            2
% 3.65/0.99  epr:                                    0
% 3.65/0.99  horn:                                   14
% 3.65/0.99  ground:                                 7
% 3.65/0.99  unary:                                  4
% 3.65/0.99  binary:                                 2
% 3.65/0.99  lits:                                   34
% 3.65/0.99  lits_eq:                                14
% 3.65/0.99  fd_pure:                                0
% 3.65/0.99  fd_pseudo:                              0
% 3.65/0.99  fd_cond:                                0
% 3.65/0.99  fd_pseudo_cond:                         0
% 3.65/0.99  ac_symbols:                             0
% 3.65/0.99  
% 3.65/0.99  ------ Propositional Solver
% 3.65/0.99  
% 3.65/0.99  prop_solver_calls:                      30
% 3.65/0.99  prop_fast_solver_calls:                 855
% 3.65/0.99  smt_solver_calls:                       0
% 3.65/0.99  smt_fast_solver_calls:                  0
% 3.65/0.99  prop_num_of_clauses:                    2945
% 3.65/0.99  prop_preprocess_simplified:             7374
% 3.65/0.99  prop_fo_subsumed:                       54
% 3.65/0.99  prop_solver_time:                       0.
% 3.65/0.99  smt_solver_time:                        0.
% 3.65/0.99  smt_fast_solver_time:                   0.
% 3.65/0.99  prop_fast_solver_time:                  0.
% 3.65/0.99  prop_unsat_core_time:                   0.
% 3.65/0.99  
% 3.65/0.99  ------ QBF
% 3.65/0.99  
% 3.65/0.99  qbf_q_res:                              0
% 3.65/0.99  qbf_num_tautologies:                    0
% 3.65/0.99  qbf_prep_cycles:                        0
% 3.65/0.99  
% 3.65/0.99  ------ BMC1
% 3.65/0.99  
% 3.65/0.99  bmc1_current_bound:                     -1
% 3.65/0.99  bmc1_last_solved_bound:                 -1
% 3.65/0.99  bmc1_unsat_core_size:                   -1
% 3.65/0.99  bmc1_unsat_core_parents_size:           -1
% 3.65/0.99  bmc1_merge_next_fun:                    0
% 3.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation
% 3.65/0.99  
% 3.65/0.99  inst_num_of_clauses:                    1446
% 3.65/0.99  inst_num_in_passive:                    275
% 3.65/0.99  inst_num_in_active:                     570
% 3.65/0.99  inst_num_in_unprocessed:                601
% 3.65/0.99  inst_num_of_loops:                      580
% 3.65/0.99  inst_num_of_learning_restarts:          0
% 3.65/0.99  inst_num_moves_active_passive:          6
% 3.65/0.99  inst_lit_activity:                      0
% 3.65/0.99  inst_lit_activity_moves:                0
% 3.65/0.99  inst_num_tautologies:                   0
% 3.65/0.99  inst_num_prop_implied:                  0
% 3.65/0.99  inst_num_existing_simplified:           0
% 3.65/0.99  inst_num_eq_res_simplified:             0
% 3.65/0.99  inst_num_child_elim:                    0
% 3.65/0.99  inst_num_of_dismatching_blockings:      1778
% 3.65/0.99  inst_num_of_non_proper_insts:           2066
% 3.65/0.99  inst_num_of_duplicates:                 0
% 3.65/0.99  inst_inst_num_from_inst_to_res:         0
% 3.65/0.99  inst_dismatching_checking_time:         0.
% 3.65/0.99  
% 3.65/0.99  ------ Resolution
% 3.65/0.99  
% 3.65/0.99  res_num_of_clauses:                     0
% 3.65/0.99  res_num_in_passive:                     0
% 3.65/0.99  res_num_in_active:                      0
% 3.65/0.99  res_num_of_loops:                       86
% 3.65/0.99  res_forward_subset_subsumed:            106
% 3.65/0.99  res_backward_subset_subsumed:           2
% 3.65/0.99  res_forward_subsumed:                   0
% 3.65/0.99  res_backward_subsumed:                  0
% 3.65/0.99  res_forward_subsumption_resolution:     0
% 3.65/0.99  res_backward_subsumption_resolution:    0
% 3.65/0.99  res_clause_to_clause_subsumption:       350
% 3.65/0.99  res_orphan_elimination:                 0
% 3.65/0.99  res_tautology_del:                      376
% 3.65/0.99  res_num_eq_res_simplified:              1
% 3.65/0.99  res_num_sel_changes:                    0
% 3.65/0.99  res_moves_from_active_to_pass:          0
% 3.65/0.99  
% 3.65/0.99  ------ Superposition
% 3.65/0.99  
% 3.65/0.99  sup_time_total:                         0.
% 3.65/0.99  sup_time_generating:                    0.
% 3.65/0.99  sup_time_sim_full:                      0.
% 3.65/0.99  sup_time_sim_immed:                     0.
% 3.65/0.99  
% 3.65/0.99  sup_num_of_clauses:                     158
% 3.65/0.99  sup_num_in_active:                      112
% 3.65/0.99  sup_num_in_passive:                     46
% 3.65/0.99  sup_num_of_loops:                       115
% 3.65/0.99  sup_fw_superposition:                   133
% 3.65/0.99  sup_bw_superposition:                   20
% 3.65/0.99  sup_immediate_simplified:               34
% 3.65/0.99  sup_given_eliminated:                   0
% 3.65/0.99  comparisons_done:                       0
% 3.65/0.99  comparisons_avoided:                    0
% 3.65/0.99  
% 3.65/0.99  ------ Simplifications
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  sim_fw_subset_subsumed:                 3
% 3.65/0.99  sim_bw_subset_subsumed:                 0
% 3.65/0.99  sim_fw_subsumed:                        0
% 3.65/0.99  sim_bw_subsumed:                        0
% 3.65/0.99  sim_fw_subsumption_res:                 0
% 3.65/0.99  sim_bw_subsumption_res:                 0
% 3.65/0.99  sim_tautology_del:                      0
% 3.65/0.99  sim_eq_tautology_del:                   2
% 3.65/0.99  sim_eq_res_simp:                        0
% 3.65/0.99  sim_fw_demodulated:                     18
% 3.65/0.99  sim_bw_demodulated:                     4
% 3.65/0.99  sim_light_normalised:                   14
% 3.65/0.99  sim_joinable_taut:                      0
% 3.65/0.99  sim_joinable_simp:                      0
% 3.65/0.99  sim_ac_normalised:                      0
% 3.65/0.99  sim_smt_subsumption:                    0
% 3.65/0.99  
%------------------------------------------------------------------------------
