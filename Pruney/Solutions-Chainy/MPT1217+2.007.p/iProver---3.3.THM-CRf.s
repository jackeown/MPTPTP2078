%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:23 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  164 (1215 expanded)
%              Number of clauses        :  107 ( 289 expanded)
%              Number of leaves         :   12 ( 363 expanded)
%              Depth                    :   25
%              Number of atoms          :  738 (7924 expanded)
%              Number of equality atoms :  111 ( 203 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f36,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35,f34,f33])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f38,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
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

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_766,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_945,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_765,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_946,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_8,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_259,c_8])).

cnf(c_20,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_20])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_21,c_18])).

cnf(c_763,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
    | k3_lattices(sK0,X0_48,X1_48) = k1_lattices(sK0,X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_948,plain,
    ( k3_lattices(sK0,X0_48,X1_48) = k1_lattices(sK0,X0_48,X1_48)
    | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1095,plain,
    ( k3_lattices(sK0,sK1,X0_48) = k1_lattices(sK0,sK1,X0_48)
    | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_948])).

cnf(c_1312,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_945,c_1095])).

cnf(c_6,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_294,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_569,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X2) = X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_21])).

cnf(c_570,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_18])).

cnf(c_575,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1 ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_15,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_376,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_377,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | v9_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_68,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_379,plain,
    ( v9_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_21,c_20,c_18,c_68])).

cnf(c_418,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_379])).

cnf(c_419,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_62,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_65,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_423,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_21,c_20,c_18,c_62,c_65])).

cnf(c_424,plain,
    ( ~ r3_lattices(sK0,X0,X1)
    | r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_423])).

cnf(c_525,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_424])).

cnf(c_526,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_528,plain,
    ( r1_lattices(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_17,c_16])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) = X1
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_528])).

cnf(c_657,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_659,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_17,c_16])).

cnf(c_759,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2 ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_1322,plain,
    ( k3_lattices(sK0,sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1312,c_759])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_21,c_20,c_18])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0_48),k7_lattices(sK0,X1_48)) = k7_lattices(sK0,k3_lattices(sK0,X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_947,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_48),k7_lattices(sK0,X1_48)) = k7_lattices(sK0,k3_lattices(sK0,X0_48,X1_48))
    | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_1227,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,X0_48)) = k7_lattices(sK0,k3_lattices(sK0,sK1,X0_48))
    | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_947])).

cnf(c_1403,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_945,c_1227])).

cnf(c_1475,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_1322,c_1403])).

cnf(c_12,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_365,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_366,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_368,plain,
    ( v8_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_21,c_20,c_18,c_65])).

cnf(c_476,plain,
    ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_368])).

cnf(c_477,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_21,c_20,c_18,c_62])).

cnf(c_482,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_481])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | X0 != X2
    | k4_lattices(sK0,X0,X3) != X1
    | k1_lattices(sK0,X1,X2) = X2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_482])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
    | k1_lattices(sK0,k4_lattices(sK0,X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,X0_48,X1_48),u1_struct_0(sK0))
    | k1_lattices(sK0,k4_lattices(sK0,X0_48,X1_48),X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_950,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,X0_48,X1_48),X0_48) = X0_48
    | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k4_lattices(sK0,X0_48,X1_48),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_1653,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK1)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_950])).

cnf(c_1657,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK1)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1653,c_1475])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_18])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_48),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_599])).

cnf(c_1025,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1026,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_5,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_317,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(resolution,[status(thm)],[c_8,c_5])).

cnf(c_545,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_21])).

cnf(c_546,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattices(sK0,X0,X1)
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_18])).

cnf(c_551,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1 ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_14,negated_conjecture,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_442,plain,
    ( r3_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_379])).

cnf(c_443,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_447,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_21,c_20,c_18,c_62,c_65])).

cnf(c_448,plain,
    ( r3_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_512,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != X1
    | k7_lattices(sK0,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_448])).

cnf(c_513,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1
    | k7_lattices(sK0,sK1) != X1
    | k7_lattices(sK0,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_551,c_513])).

cnf(c_644,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_760,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_644])).

cnf(c_790,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_48),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_792,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_791,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1657,c_1026,c_1025,c_760,c_792,c_791,c_27,c_16,c_26,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.32/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.00  
% 2.32/1.00  ------  iProver source info
% 2.32/1.00  
% 2.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.00  git: non_committed_changes: false
% 2.32/1.00  git: last_make_outside_of_git: false
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     num_symb
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       true
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 11
% 2.32/1.00  conjectures                             2
% 2.32/1.00  EPR                                     0
% 2.32/1.00  Horn                                    11
% 2.32/1.00  unary                                   3
% 2.32/1.00  binary                                  2
% 2.32/1.00  lits                                    26
% 2.32/1.00  lits eq                                 8
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 0
% 2.32/1.00  fd_pseudo_cond                          0
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status Theorem for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f9,conjecture,(
% 2.32/1.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f10,negated_conjecture,(
% 2.32/1.00    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.32/1.00    inference(negated_conjecture,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ( ! [X0,X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,sK2) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1)) & r3_lattices(X0,sK1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f33,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f36,plain,(
% 2.32/1.00    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35,f34,f33])).
% 2.32/1.00  
% 2.32/1.00  fof(f56,plain,(
% 2.32/1.00    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f12,plain,(
% 2.32/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f13,plain,(
% 2.32/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.32/1.00  
% 2.32/1.00  fof(f14,plain,(
% 2.32/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,plain,(
% 2.32/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.32/1.00    inference(flattening,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f38,plain,(
% 2.32/1.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f21])).
% 2.32/1.00  
% 2.32/1.00  fof(f46,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f11,plain,(
% 2.32/1.00    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f52,plain,(
% 2.32/1.00    v10_lattices(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    ~v2_struct_0(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f54,plain,(
% 2.32/1.00    l3_lattices(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f2,axiom,(
% 2.32/1.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f16,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f2])).
% 2.32/1.00  
% 2.32/1.00  fof(f17,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f31,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f42,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f31])).
% 2.32/1.00  
% 2.32/1.00  fof(f57,plain,(
% 2.32/1.00    r3_lattices(sK0,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f32,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f47,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f32])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f40,plain,(
% 2.32/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f8,axiom,(
% 2.32/1.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f8])).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    v17_lattices(sK0)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f7,axiom,(
% 2.32/1.00    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f7])).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f25])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f26])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f18,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f31])).
% 2.32/1.00  
% 2.32/1.00  fof(f58,plain,(
% 2.32/1.00    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f32])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_16,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_766,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_945,plain,
% 2.32/1.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_17,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_765,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_946,plain,
% 2.32/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3,plain,
% 2.32/1.00      ( v4_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v10_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_9,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l2_lattices(X1)
% 2.32/1.00      | ~ v4_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_258,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l2_lattices(X1)
% 2.32/1.00      | ~ l3_lattices(X3)
% 2.32/1.00      | v2_struct_0(X3)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v10_lattices(X3)
% 2.32/1.00      | X1 != X3
% 2.32/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_259,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l2_lattices(X1)
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v10_lattices(X1)
% 2.32/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_258]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_8,plain,
% 2.32/1.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_277,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v10_lattices(X1)
% 2.32/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) ),
% 2.32/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_259,c_8]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_20,negated_conjecture,
% 2.32/1.00      ( v10_lattices(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_387,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
% 2.32/1.00      | sK0 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_277,c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_388,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0)
% 2.32/1.00      | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_21,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_18,negated_conjecture,
% 2.32/1.00      ( l3_lattices(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_392,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_388,c_21,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_763,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
% 2.32/1.00      | k3_lattices(sK0,X0_48,X1_48) = k1_lattices(sK0,X0_48,X1_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_392]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_948,plain,
% 2.32/1.00      ( k3_lattices(sK0,X0_48,X1_48) = k1_lattices(sK0,X0_48,X1_48)
% 2.32/1.00      | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1095,plain,
% 2.32/1.00      ( k3_lattices(sK0,sK1,X0_48) = k1_lattices(sK0,sK1,X0_48)
% 2.32/1.00      | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_946,c_948]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1312,plain,
% 2.32/1.00      ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_945,c_1095]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_6,plain,
% 2.32/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l2_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) = X2 ),
% 2.32/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_294,plain,
% 2.32/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) = X2 ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_569,plain,
% 2.32/1.00      ( ~ r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) = X2
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_294,c_21]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_570,plain,
% 2.32/1.00      ( ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_574,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_570,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_575,plain,
% 2.32/1.00      ( ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,X0,X1) = X1 ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_574]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_15,negated_conjecture,
% 2.32/1.00      ( r3_lattices(sK0,sK1,sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_11,plain,
% 2.32/1.00      ( ~ r3_lattices(X0,X1,X2)
% 2.32/1.00      | r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v9_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v10_lattices(X0)
% 2.32/1.00      | v9_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_376,plain,
% 2.32/1.00      ( ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | v9_lattices(X0)
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_377,plain,
% 2.32/1.00      ( ~ l3_lattices(sK0) | v2_struct_0(sK0) | v9_lattices(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_376]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_68,plain,
% 2.32/1.00      ( ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0)
% 2.32/1.00      | ~ v10_lattices(sK0)
% 2.32/1.00      | v9_lattices(sK0) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_379,plain,
% 2.32/1.00      ( v9_lattices(sK0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_377,c_21,c_20,c_18,c_68]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_418,plain,
% 2.32/1.00      ( ~ r3_lattices(X0,X1,X2)
% 2.32/1.00      | r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_379]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_419,plain,
% 2.32/1.00      ( ~ r3_lattices(sK0,X0,X1)
% 2.32/1.00      | r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ v6_lattices(sK0)
% 2.32/1.00      | ~ v8_lattices(sK0)
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_418]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2,plain,
% 2.32/1.00      ( v6_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v10_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_62,plain,
% 2.32/1.00      ( v6_lattices(sK0)
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0)
% 2.32/1.00      | ~ v10_lattices(sK0) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1,plain,
% 2.32/1.00      ( v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v10_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_65,plain,
% 2.32/1.00      ( v8_lattices(sK0)
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0)
% 2.32/1.00      | ~ v10_lattices(sK0) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_423,plain,
% 2.32/1.00      ( ~ r3_lattices(sK0,X0,X1)
% 2.32/1.00      | r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_419,c_21,c_20,c_18,c_62,c_65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_424,plain,
% 2.32/1.00      ( ~ r3_lattices(sK0,X0,X1)
% 2.32/1.00      | r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_423]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_525,plain,
% 2.32/1.00      ( r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | sK1 != X0
% 2.32/1.00      | sK2 != X1
% 2.32/1.00      | sK0 != sK0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_424]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_526,plain,
% 2.32/1.00      ( r1_lattices(sK0,sK1,sK2)
% 2.32/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_528,plain,
% 2.32/1.00      ( r1_lattices(sK0,sK1,sK2) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_526,c_17,c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_656,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,X0,X1) = X1
% 2.32/1.00      | sK1 != X0
% 2.32/1.00      | sK2 != X1
% 2.32/1.00      | sK0 != sK0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_575,c_528]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_657,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,sK1,sK2) = sK2 ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_656]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_659,plain,
% 2.32/1.00      ( k1_lattices(sK0,sK1,sK2) = sK2 ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_657,c_17,c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_759,plain,
% 2.32/1.00      ( k1_lattices(sK0,sK1,sK2) = sK2 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_659]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1322,plain,
% 2.32/1.00      ( k3_lattices(sK0,sK1,sK2) = sK2 ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1312,c_759]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ v17_lattices(X1)
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v10_lattices(X1)
% 2.32/1.00      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_19,negated_conjecture,
% 2.32/1.00      ( v17_lattices(sK0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_233,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v10_lattices(X1)
% 2.32/1.00      | k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k3_lattices(X1,X2,X0))
% 2.32/1.00      | sK0 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_234,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0)
% 2.32/1.00      | ~ v10_lattices(sK0)
% 2.32/1.00      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_233]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_238,plain,
% 2.32/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_234,c_21,c_20,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_239,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k4_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k3_lattices(sK0,X0,X1)) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_238]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_764,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
% 2.32/1.00      | k4_lattices(sK0,k7_lattices(sK0,X0_48),k7_lattices(sK0,X1_48)) = k7_lattices(sK0,k3_lattices(sK0,X0_48,X1_48)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_239]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_947,plain,
% 2.32/1.00      ( k4_lattices(sK0,k7_lattices(sK0,X0_48),k7_lattices(sK0,X1_48)) = k7_lattices(sK0,k3_lattices(sK0,X0_48,X1_48))
% 2.32/1.00      | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1227,plain,
% 2.32/1.00      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,X0_48)) = k7_lattices(sK0,k3_lattices(sK0,sK1,X0_48))
% 2.32/1.00      | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_946,c_947]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1403,plain,
% 2.32/1.00      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_945,c_1227]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1475,plain,
% 2.32/1.00      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,sK2) ),
% 2.32/1.00      inference(demodulation,[status(thm)],[c_1322,c_1403]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_365,plain,
% 2.32/1.00      ( v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_366,plain,
% 2.32/1.00      ( v8_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_368,plain,
% 2.32/1.00      ( v8_lattices(sK0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_366,c_21,c_20,c_18,c_65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_476,plain,
% 2.32/1.00      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_368]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_477,plain,
% 2.32/1.00      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ v6_lattices(sK0)
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_481,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_477,c_21,c_20,c_18,c_62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_482,plain,
% 2.32/1.00      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_481]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_625,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK0))
% 2.32/1.00      | X0 != X2
% 2.32/1.00      | k4_lattices(sK0,X0,X3) != X1
% 2.32/1.00      | k1_lattices(sK0,X1,X2) = X2
% 2.32/1.00      | sK0 != sK0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_575,c_482]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_626,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,k4_lattices(sK0,X0,X1),X0) = X0 ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_625]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_761,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(k4_lattices(sK0,X0_48,X1_48),u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,k4_lattices(sK0,X0_48,X1_48),X0_48) = X0_48 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_626]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_950,plain,
% 2.32/1.00      ( k1_lattices(sK0,k4_lattices(sK0,X0_48,X1_48),X0_48) = X0_48
% 2.32/1.00      | m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(X1_48,u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(k4_lattices(sK0,X0_48,X1_48),u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1653,plain,
% 2.32/1.00      ( k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK1)
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1475,c_950]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1657,plain,
% 2.32/1.00      ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,sK1)
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1653,c_1475]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | v2_struct_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_593,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 2.32/1.00      | ~ l3_lattices(X1)
% 2.32/1.00      | sK0 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_594,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 2.32/1.00      | ~ l3_lattices(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_593]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_598,plain,
% 2.32/1.00      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_594,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_599,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_598]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_762,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,u1_struct_0(sK0))
% 2.32/1.00      | m1_subset_1(k7_lattices(sK0,X0_48),u1_struct_0(sK0)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_599]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1025,plain,
% 2.32/1.00      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_762]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1026,plain,
% 2.32/1.00      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 2.32/1.00      | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5,plain,
% 2.32/1.00      ( r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l2_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) != X2 ),
% 2.32/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_317,plain,
% 2.32/1.00      ( r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) != X2 ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_8,c_5]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_545,plain,
% 2.32/1.00      ( r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | k1_lattices(X0,X1,X2) != X2
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_317,c_21]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_546,plain,
% 2.32/1.00      ( r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | k1_lattices(sK0,X0,X1) != X1 ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_545]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_550,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | r1_lattices(sK0,X0,X1)
% 2.32/1.00      | k1_lattices(sK0,X0,X1) != X1 ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_546,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_551,plain,
% 2.32/1.00      ( r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k1_lattices(sK0,X0,X1) != X1 ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_550]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,negated_conjecture,
% 2.32/1.00      ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_10,plain,
% 2.32/1.00      ( r3_lattices(X0,X1,X2)
% 2.32/1.00      | ~ r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v9_lattices(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_442,plain,
% 2.32/1.00      ( r3_lattices(X0,X1,X2)
% 2.32/1.00      | ~ r1_lattices(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | ~ v6_lattices(X0)
% 2.32/1.00      | ~ v8_lattices(X0)
% 2.32/1.00      | ~ l3_lattices(X0)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | sK0 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_379]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_443,plain,
% 2.32/1.00      ( r3_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ v6_lattices(sK0)
% 2.32/1.00      | ~ v8_lattices(sK0)
% 2.32/1.00      | ~ l3_lattices(sK0)
% 2.32/1.00      | v2_struct_0(sK0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_442]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_447,plain,
% 2.32/1.00      ( r3_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_443,c_21,c_20,c_18,c_62,c_65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_448,plain,
% 2.32/1.00      ( r3_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_447]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_512,plain,
% 2.32/1.00      ( ~ r1_lattices(sK0,X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.00      | k7_lattices(sK0,sK1) != X1
% 2.32/1.00      | k7_lattices(sK0,sK2) != X0
% 2.32/1.00      | sK0 != sK0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_448]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_513,plain,
% 2.32/1.00      ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
% 2.32/1.00      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 2.32/1.00      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_643,plain,
% 2.32/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.32/1.01      | k1_lattices(sK0,X0,X1) != X1
% 2.32/1.01      | k7_lattices(sK0,sK1) != X1
% 2.32/1.01      | k7_lattices(sK0,sK2) != X0
% 2.32/1.01      | sK0 != sK0 ),
% 2.32/1.01      inference(resolution_lifted,[status(thm)],[c_551,c_513]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_644,plain,
% 2.32/1.01      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.32/1.01      | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
% 2.32/1.01      inference(unflattening,[status(thm)],[c_643]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_760,plain,
% 2.32/1.01      ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 2.32/1.01      | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) != k7_lattices(sK0,sK1) ),
% 2.32/1.01      inference(subtyping,[status(esa)],[c_644]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_790,plain,
% 2.32/1.01      ( m1_subset_1(X0_48,u1_struct_0(sK0)) != iProver_top
% 2.32/1.01      | m1_subset_1(k7_lattices(sK0,X0_48),u1_struct_0(sK0)) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_792,plain,
% 2.32/1.01      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 2.32/1.01      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_790]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_791,plain,
% 2.32/1.01      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 2.32/1.01      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_762]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_27,plain,
% 2.32/1.01      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_26,plain,
% 2.32/1.01      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.32/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(contradiction,plain,
% 2.32/1.01      ( $false ),
% 2.32/1.01      inference(minisat,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_1657,c_1026,c_1025,c_760,c_792,c_791,c_27,c_16,c_26,
% 2.32/1.01                 c_17]) ).
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  ------                               Statistics
% 2.32/1.01  
% 2.32/1.01  ------ General
% 2.32/1.01  
% 2.32/1.01  abstr_ref_over_cycles:                  0
% 2.32/1.01  abstr_ref_under_cycles:                 0
% 2.32/1.01  gc_basic_clause_elim:                   0
% 2.32/1.01  forced_gc_time:                         0
% 2.32/1.01  parsing_time:                           0.009
% 2.32/1.01  unif_index_cands_time:                  0.
% 2.32/1.01  unif_index_add_time:                    0.
% 2.32/1.01  orderings_time:                         0.
% 2.32/1.01  out_proof_time:                         0.013
% 2.32/1.01  total_time:                             0.09
% 2.32/1.01  num_of_symbols:                         52
% 2.32/1.01  num_of_terms:                           1315
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing
% 2.32/1.01  
% 2.32/1.01  num_of_splits:                          1
% 2.32/1.01  num_of_split_atoms:                     1
% 2.32/1.01  num_of_reused_defs:                     0
% 2.32/1.01  num_eq_ax_congr_red:                    24
% 2.32/1.01  num_of_sem_filtered_clauses:            1
% 2.32/1.01  num_of_subtypes:                        3
% 2.32/1.01  monotx_restored_types:                  0
% 2.32/1.01  sat_num_of_epr_types:                   0
% 2.32/1.01  sat_num_of_non_cyclic_types:            0
% 2.32/1.01  sat_guarded_non_collapsed_types:        1
% 2.32/1.01  num_pure_diseq_elim:                    0
% 2.32/1.01  simp_replaced_by:                       0
% 2.32/1.01  res_preprocessed:                       66
% 2.32/1.01  prep_upred:                             0
% 2.32/1.01  prep_unflattend:                        23
% 2.32/1.01  smt_new_axioms:                         0
% 2.32/1.01  pred_elim_cands:                        1
% 2.32/1.01  pred_elim:                              11
% 2.32/1.01  pred_elim_cl:                           11
% 2.32/1.01  pred_elim_cycles:                       13
% 2.32/1.01  merged_defs:                            0
% 2.32/1.01  merged_defs_ncl:                        0
% 2.32/1.01  bin_hyper_res:                          0
% 2.32/1.01  prep_cycles:                            4
% 2.32/1.01  pred_elim_time:                         0.009
% 2.32/1.01  splitting_time:                         0.
% 2.32/1.01  sem_filter_time:                        0.
% 2.32/1.01  monotx_time:                            0.
% 2.32/1.01  subtype_inf_time:                       0.
% 2.32/1.01  
% 2.32/1.01  ------ Problem properties
% 2.32/1.01  
% 2.32/1.01  clauses:                                11
% 2.32/1.01  conjectures:                            2
% 2.32/1.01  epr:                                    0
% 2.32/1.01  horn:                                   11
% 2.32/1.01  ground:                                 6
% 2.32/1.01  unary:                                  3
% 2.32/1.01  binary:                                 2
% 2.32/1.01  lits:                                   26
% 2.32/1.01  lits_eq:                                8
% 2.32/1.01  fd_pure:                                0
% 2.32/1.01  fd_pseudo:                              0
% 2.32/1.01  fd_cond:                                0
% 2.32/1.01  fd_pseudo_cond:                         0
% 2.32/1.01  ac_symbols:                             0
% 2.32/1.01  
% 2.32/1.01  ------ Propositional Solver
% 2.32/1.01  
% 2.32/1.01  prop_solver_calls:                      27
% 2.32/1.01  prop_fast_solver_calls:                 537
% 2.32/1.01  smt_solver_calls:                       0
% 2.32/1.01  smt_fast_solver_calls:                  0
% 2.32/1.01  prop_num_of_clauses:                    499
% 2.32/1.01  prop_preprocess_simplified:             1985
% 2.32/1.01  prop_fo_subsumed:                       31
% 2.32/1.01  prop_solver_time:                       0.
% 2.32/1.01  smt_solver_time:                        0.
% 2.32/1.01  smt_fast_solver_time:                   0.
% 2.32/1.01  prop_fast_solver_time:                  0.
% 2.32/1.01  prop_unsat_core_time:                   0.
% 2.32/1.01  
% 2.32/1.01  ------ QBF
% 2.32/1.01  
% 2.32/1.01  qbf_q_res:                              0
% 2.32/1.01  qbf_num_tautologies:                    0
% 2.32/1.01  qbf_prep_cycles:                        0
% 2.32/1.01  
% 2.32/1.01  ------ BMC1
% 2.32/1.01  
% 2.32/1.01  bmc1_current_bound:                     -1
% 2.32/1.01  bmc1_last_solved_bound:                 -1
% 2.32/1.01  bmc1_unsat_core_size:                   -1
% 2.32/1.01  bmc1_unsat_core_parents_size:           -1
% 2.32/1.01  bmc1_merge_next_fun:                    0
% 2.32/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation
% 2.32/1.01  
% 2.32/1.01  inst_num_of_clauses:                    142
% 2.32/1.01  inst_num_in_passive:                    21
% 2.32/1.01  inst_num_in_active:                     100
% 2.32/1.01  inst_num_in_unprocessed:                21
% 2.32/1.01  inst_num_of_loops:                      110
% 2.32/1.01  inst_num_of_learning_restarts:          0
% 2.32/1.01  inst_num_moves_active_passive:          6
% 2.32/1.01  inst_lit_activity:                      0
% 2.32/1.01  inst_lit_activity_moves:                0
% 2.32/1.01  inst_num_tautologies:                   0
% 2.32/1.01  inst_num_prop_implied:                  0
% 2.32/1.01  inst_num_existing_simplified:           0
% 2.32/1.01  inst_num_eq_res_simplified:             0
% 2.32/1.01  inst_num_child_elim:                    0
% 2.32/1.01  inst_num_of_dismatching_blockings:      44
% 2.32/1.01  inst_num_of_non_proper_insts:           163
% 2.32/1.01  inst_num_of_duplicates:                 0
% 2.32/1.01  inst_inst_num_from_inst_to_res:         0
% 2.32/1.01  inst_dismatching_checking_time:         0.
% 2.32/1.01  
% 2.32/1.01  ------ Resolution
% 2.32/1.01  
% 2.32/1.01  res_num_of_clauses:                     0
% 2.32/1.01  res_num_in_passive:                     0
% 2.32/1.01  res_num_in_active:                      0
% 2.32/1.01  res_num_of_loops:                       70
% 2.32/1.01  res_forward_subset_subsumed:            19
% 2.32/1.01  res_backward_subset_subsumed:           0
% 2.32/1.01  res_forward_subsumed:                   0
% 2.32/1.01  res_backward_subsumed:                  0
% 2.32/1.01  res_forward_subsumption_resolution:     1
% 2.32/1.01  res_backward_subsumption_resolution:    0
% 2.32/1.01  res_clause_to_clause_subsumption:       69
% 2.32/1.01  res_orphan_elimination:                 0
% 2.32/1.01  res_tautology_del:                      39
% 2.32/1.01  res_num_eq_res_simplified:              1
% 2.32/1.01  res_num_sel_changes:                    0
% 2.32/1.01  res_moves_from_active_to_pass:          0
% 2.32/1.01  
% 2.32/1.01  ------ Superposition
% 2.32/1.01  
% 2.32/1.01  sup_time_total:                         0.
% 2.32/1.01  sup_time_generating:                    0.
% 2.32/1.01  sup_time_sim_full:                      0.
% 2.32/1.01  sup_time_sim_immed:                     0.
% 2.32/1.01  
% 2.32/1.01  sup_num_of_clauses:                     33
% 2.32/1.01  sup_num_in_active:                      21
% 2.32/1.01  sup_num_in_passive:                     12
% 2.32/1.01  sup_num_of_loops:                       21
% 2.32/1.01  sup_fw_superposition:                   25
% 2.32/1.01  sup_bw_superposition:                   0
% 2.32/1.01  sup_immediate_simplified:               8
% 2.32/1.01  sup_given_eliminated:                   0
% 2.32/1.01  comparisons_done:                       0
% 2.32/1.01  comparisons_avoided:                    0
% 2.32/1.01  
% 2.32/1.01  ------ Simplifications
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  sim_fw_subset_subsumed:                 0
% 2.32/1.01  sim_bw_subset_subsumed:                 0
% 2.32/1.01  sim_fw_subsumed:                        0
% 2.32/1.01  sim_bw_subsumed:                        0
% 2.32/1.01  sim_fw_subsumption_res:                 0
% 2.32/1.01  sim_bw_subsumption_res:                 0
% 2.32/1.01  sim_tautology_del:                      0
% 2.32/1.01  sim_eq_tautology_del:                   0
% 2.32/1.01  sim_eq_res_simp:                        0
% 2.32/1.01  sim_fw_demodulated:                     0
% 2.32/1.01  sim_bw_demodulated:                     1
% 2.32/1.01  sim_light_normalised:                   8
% 2.32/1.01  sim_joinable_taut:                      0
% 2.32/1.01  sim_joinable_simp:                      0
% 2.32/1.01  sim_ac_normalised:                      0
% 2.32/1.01  sim_smt_subsumption:                    0
% 2.32/1.01  
%------------------------------------------------------------------------------
