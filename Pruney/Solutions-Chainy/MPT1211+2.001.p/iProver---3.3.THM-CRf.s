%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:21 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 321 expanded)
%              Number of clauses        :   63 (  89 expanded)
%              Number of leaves         :   12 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  536 (1653 expanded)
%              Number of equality atoms :  118 ( 312 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,sK1),sK1)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f36,f35])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

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
       => ( v8_lattices(X0)
          & v7_lattices(X0)
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
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_lattices(X0,X1) = X2
                  | ~ r2_lattices(X0,X2,X1) )
                & ( r2_lattices(X0,X2,X1)
                  | k7_lattices(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f41,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k2_lattices(X0,X2,X1) != k5_lattices(X0)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k1_lattices(X0,X2,X1) != k6_lattices(X0)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k2_lattices(X0,X2,X1) != k5_lattices(X0)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k1_lattices(X0,X2,X1) != k6_lattices(X0)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k2_lattices(X0,X2,X1) = k5_lattices(X0)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k1_lattices(X0,X2,X1) = k6_lattices(X0)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_751,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_999,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != X0_51
    | k5_lattices(sK0) != X0_51
    | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1077,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47)
    | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1078,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_1032,plain,
    ( X0_51 != X1_51
    | k5_lattices(sK0) != X1_51
    | k5_lattices(sK0) = X0_51 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1061,plain,
    ( X0_51 != k5_lattices(sK0)
    | k5_lattices(sK0) = X0_51
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1067,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) != k5_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47)
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1068,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k5_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_748,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1031,plain,
    ( k5_lattices(sK0) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_17,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_500,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_17])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_47),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_917,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_47),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_19,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v6_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | X1 != X3
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_14])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_234])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_265])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_20,c_17])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
    | k4_lattices(sK0,X1_47,X0_47) = k2_lattices(sK0,X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_355])).

cnf(c_916,plain,
    ( k4_lattices(sK0,X0_47,X1_47) = k2_lattices(sK0,X0_47,X1_47)
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1015,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_47),X1_47) = k2_lattices(sK0,k7_lattices(sK0,X0_47),X1_47)
    | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_916])).

cnf(c_1028,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_11,plain,
    ( r2_lattices(X0,k7_lattices(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
    | ~ v11_lattices(X0)
    | ~ v16_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( ~ v17_lattices(X0)
    | v16_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_218,plain,
    ( v16_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_219,plain,
    ( v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_57,plain,
    ( ~ v17_lattices(sK0)
    | v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_221,plain,
    ( v16_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_20,c_18,c_17,c_57])).

cnf(c_295,plain,
    ( r2_lattices(X0,k7_lattices(X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
    | ~ v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_221])).

cnf(c_296,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_3,plain,
    ( v11_lattices(X0)
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_54,plain,
    ( v11_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_300,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_20,c_19,c_18,c_17,c_54])).

cnf(c_543,plain,
    ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_501,c_300])).

cnf(c_7,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | k2_lattices(X0,X1,X2) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_418,plain,
    ( ~ r2_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k2_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_419,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,X0,X1)
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_17])).

cnf(c_424,plain,
    ( ~ r2_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_423])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | X2 != X1
    | k2_lattices(sK0,X0,X2) = k5_lattices(sK0)
    | k7_lattices(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_543,c_424])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_17,c_496])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_601])).

cnf(c_780,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_15,negated_conjecture,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_744,negated_conjecture,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1078,c_1068,c_1031,c_1028,c_780,c_744,c_25,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.93/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.93/1.02  
% 0.93/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.93/1.02  
% 0.93/1.02  ------  iProver source info
% 0.93/1.02  
% 0.93/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.93/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.93/1.02  git: non_committed_changes: false
% 0.93/1.02  git: last_make_outside_of_git: false
% 0.93/1.02  
% 0.93/1.02  ------ 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options
% 0.93/1.02  
% 0.93/1.02  --out_options                           all
% 0.93/1.02  --tptp_safe_out                         true
% 0.93/1.02  --problem_path                          ""
% 0.93/1.02  --include_path                          ""
% 0.93/1.02  --clausifier                            res/vclausify_rel
% 0.93/1.02  --clausifier_options                    --mode clausify
% 0.93/1.02  --stdin                                 false
% 0.93/1.02  --stats_out                             all
% 0.93/1.02  
% 0.93/1.02  ------ General Options
% 0.93/1.02  
% 0.93/1.02  --fof                                   false
% 0.93/1.02  --time_out_real                         305.
% 0.93/1.02  --time_out_virtual                      -1.
% 0.93/1.02  --symbol_type_check                     false
% 0.93/1.02  --clausify_out                          false
% 0.93/1.02  --sig_cnt_out                           false
% 0.93/1.02  --trig_cnt_out                          false
% 0.93/1.02  --trig_cnt_out_tolerance                1.
% 0.93/1.02  --trig_cnt_out_sk_spl                   false
% 0.93/1.02  --abstr_cl_out                          false
% 0.93/1.02  
% 0.93/1.02  ------ Global Options
% 0.93/1.02  
% 0.93/1.02  --schedule                              default
% 0.93/1.02  --add_important_lit                     false
% 0.93/1.02  --prop_solver_per_cl                    1000
% 0.93/1.02  --min_unsat_core                        false
% 0.93/1.02  --soft_assumptions                      false
% 0.93/1.02  --soft_lemma_size                       3
% 0.93/1.02  --prop_impl_unit_size                   0
% 0.93/1.02  --prop_impl_unit                        []
% 0.93/1.02  --share_sel_clauses                     true
% 0.93/1.02  --reset_solvers                         false
% 0.93/1.02  --bc_imp_inh                            [conj_cone]
% 0.93/1.02  --conj_cone_tolerance                   3.
% 0.93/1.02  --extra_neg_conj                        none
% 0.93/1.02  --large_theory_mode                     true
% 0.93/1.02  --prolific_symb_bound                   200
% 0.93/1.02  --lt_threshold                          2000
% 0.93/1.02  --clause_weak_htbl                      true
% 0.93/1.02  --gc_record_bc_elim                     false
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing Options
% 0.93/1.02  
% 0.93/1.02  --preprocessing_flag                    true
% 0.93/1.02  --time_out_prep_mult                    0.1
% 0.93/1.02  --splitting_mode                        input
% 0.93/1.02  --splitting_grd                         true
% 0.93/1.02  --splitting_cvd                         false
% 0.93/1.02  --splitting_cvd_svl                     false
% 0.93/1.02  --splitting_nvd                         32
% 0.93/1.02  --sub_typing                            true
% 0.93/1.02  --prep_gs_sim                           true
% 0.93/1.02  --prep_unflatten                        true
% 0.93/1.02  --prep_res_sim                          true
% 0.93/1.02  --prep_upred                            true
% 0.93/1.02  --prep_sem_filter                       exhaustive
% 0.93/1.02  --prep_sem_filter_out                   false
% 0.93/1.02  --pred_elim                             true
% 0.93/1.02  --res_sim_input                         true
% 0.93/1.02  --eq_ax_congr_red                       true
% 0.93/1.02  --pure_diseq_elim                       true
% 0.93/1.02  --brand_transform                       false
% 0.93/1.02  --non_eq_to_eq                          false
% 0.93/1.02  --prep_def_merge                        true
% 0.93/1.02  --prep_def_merge_prop_impl              false
% 0.93/1.02  --prep_def_merge_mbd                    true
% 0.93/1.02  --prep_def_merge_tr_red                 false
% 0.93/1.02  --prep_def_merge_tr_cl                  false
% 0.93/1.02  --smt_preprocessing                     true
% 0.93/1.02  --smt_ac_axioms                         fast
% 0.93/1.02  --preprocessed_out                      false
% 0.93/1.02  --preprocessed_stats                    false
% 0.93/1.02  
% 0.93/1.02  ------ Abstraction refinement Options
% 0.93/1.02  
% 0.93/1.02  --abstr_ref                             []
% 0.93/1.02  --abstr_ref_prep                        false
% 0.93/1.02  --abstr_ref_until_sat                   false
% 0.93/1.02  --abstr_ref_sig_restrict                funpre
% 0.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.02  --abstr_ref_under                       []
% 0.93/1.02  
% 0.93/1.02  ------ SAT Options
% 0.93/1.02  
% 0.93/1.02  --sat_mode                              false
% 0.93/1.02  --sat_fm_restart_options                ""
% 0.93/1.02  --sat_gr_def                            false
% 0.93/1.02  --sat_epr_types                         true
% 0.93/1.02  --sat_non_cyclic_types                  false
% 0.93/1.02  --sat_finite_models                     false
% 0.93/1.02  --sat_fm_lemmas                         false
% 0.93/1.02  --sat_fm_prep                           false
% 0.93/1.02  --sat_fm_uc_incr                        true
% 0.93/1.02  --sat_out_model                         small
% 0.93/1.02  --sat_out_clauses                       false
% 0.93/1.02  
% 0.93/1.02  ------ QBF Options
% 0.93/1.02  
% 0.93/1.02  --qbf_mode                              false
% 0.93/1.02  --qbf_elim_univ                         false
% 0.93/1.02  --qbf_dom_inst                          none
% 0.93/1.02  --qbf_dom_pre_inst                      false
% 0.93/1.02  --qbf_sk_in                             false
% 0.93/1.02  --qbf_pred_elim                         true
% 0.93/1.02  --qbf_split                             512
% 0.93/1.02  
% 0.93/1.02  ------ BMC1 Options
% 0.93/1.02  
% 0.93/1.02  --bmc1_incremental                      false
% 0.93/1.02  --bmc1_axioms                           reachable_all
% 0.93/1.02  --bmc1_min_bound                        0
% 0.93/1.02  --bmc1_max_bound                        -1
% 0.93/1.02  --bmc1_max_bound_default                -1
% 0.93/1.02  --bmc1_symbol_reachability              true
% 0.93/1.02  --bmc1_property_lemmas                  false
% 0.93/1.02  --bmc1_k_induction                      false
% 0.93/1.02  --bmc1_non_equiv_states                 false
% 0.93/1.02  --bmc1_deadlock                         false
% 0.93/1.02  --bmc1_ucm                              false
% 0.93/1.02  --bmc1_add_unsat_core                   none
% 0.93/1.02  --bmc1_unsat_core_children              false
% 0.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.02  --bmc1_out_stat                         full
% 0.93/1.02  --bmc1_ground_init                      false
% 0.93/1.02  --bmc1_pre_inst_next_state              false
% 0.93/1.02  --bmc1_pre_inst_state                   false
% 0.93/1.02  --bmc1_pre_inst_reach_state             false
% 0.93/1.02  --bmc1_out_unsat_core                   false
% 0.93/1.02  --bmc1_aig_witness_out                  false
% 0.93/1.02  --bmc1_verbose                          false
% 0.93/1.02  --bmc1_dump_clauses_tptp                false
% 0.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.02  --bmc1_dump_file                        -
% 0.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.02  --bmc1_ucm_extend_mode                  1
% 0.93/1.02  --bmc1_ucm_init_mode                    2
% 0.93/1.02  --bmc1_ucm_cone_mode                    none
% 0.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.02  --bmc1_ucm_relax_model                  4
% 0.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.02  --bmc1_ucm_layered_model                none
% 0.93/1.02  --bmc1_ucm_max_lemma_size               10
% 0.93/1.02  
% 0.93/1.02  ------ AIG Options
% 0.93/1.02  
% 0.93/1.02  --aig_mode                              false
% 0.93/1.02  
% 0.93/1.02  ------ Instantiation Options
% 0.93/1.02  
% 0.93/1.02  --instantiation_flag                    true
% 0.93/1.02  --inst_sos_flag                         false
% 0.93/1.02  --inst_sos_phase                        true
% 0.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel_side                     num_symb
% 0.93/1.02  --inst_solver_per_active                1400
% 0.93/1.02  --inst_solver_calls_frac                1.
% 0.93/1.02  --inst_passive_queue_type               priority_queues
% 0.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.02  --inst_passive_queues_freq              [25;2]
% 0.93/1.02  --inst_dismatching                      true
% 0.93/1.02  --inst_eager_unprocessed_to_passive     true
% 0.93/1.02  --inst_prop_sim_given                   true
% 0.93/1.02  --inst_prop_sim_new                     false
% 0.93/1.02  --inst_subs_new                         false
% 0.93/1.02  --inst_eq_res_simp                      false
% 0.93/1.02  --inst_subs_given                       false
% 0.93/1.02  --inst_orphan_elimination               true
% 0.93/1.02  --inst_learning_loop_flag               true
% 0.93/1.02  --inst_learning_start                   3000
% 0.93/1.02  --inst_learning_factor                  2
% 0.93/1.02  --inst_start_prop_sim_after_learn       3
% 0.93/1.02  --inst_sel_renew                        solver
% 0.93/1.02  --inst_lit_activity_flag                true
% 0.93/1.02  --inst_restr_to_given                   false
% 0.93/1.02  --inst_activity_threshold               500
% 0.93/1.02  --inst_out_proof                        true
% 0.93/1.02  
% 0.93/1.02  ------ Resolution Options
% 0.93/1.02  
% 0.93/1.02  --resolution_flag                       true
% 0.93/1.02  --res_lit_sel                           adaptive
% 0.93/1.02  --res_lit_sel_side                      none
% 0.93/1.02  --res_ordering                          kbo
% 0.93/1.02  --res_to_prop_solver                    active
% 0.93/1.02  --res_prop_simpl_new                    false
% 0.93/1.02  --res_prop_simpl_given                  true
% 0.93/1.02  --res_passive_queue_type                priority_queues
% 0.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.02  --res_passive_queues_freq               [15;5]
% 0.93/1.02  --res_forward_subs                      full
% 0.93/1.02  --res_backward_subs                     full
% 0.93/1.02  --res_forward_subs_resolution           true
% 0.93/1.02  --res_backward_subs_resolution          true
% 0.93/1.02  --res_orphan_elimination                true
% 0.93/1.02  --res_time_limit                        2.
% 0.93/1.02  --res_out_proof                         true
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Options
% 0.93/1.02  
% 0.93/1.02  --superposition_flag                    true
% 0.93/1.02  --sup_passive_queue_type                priority_queues
% 0.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.02  --demod_completeness_check              fast
% 0.93/1.02  --demod_use_ground                      true
% 0.93/1.02  --sup_to_prop_solver                    passive
% 0.93/1.02  --sup_prop_simpl_new                    true
% 0.93/1.02  --sup_prop_simpl_given                  true
% 0.93/1.02  --sup_fun_splitting                     false
% 0.93/1.02  --sup_smt_interval                      50000
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Simplification Setup
% 0.93/1.02  
% 0.93/1.02  --sup_indices_passive                   []
% 0.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_full_bw                           [BwDemod]
% 0.93/1.02  --sup_immed_triv                        [TrivRules]
% 0.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_immed_bw_main                     []
% 0.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  
% 0.93/1.02  ------ Combination Options
% 0.93/1.02  
% 0.93/1.02  --comb_res_mult                         3
% 0.93/1.02  --comb_sup_mult                         2
% 0.93/1.02  --comb_inst_mult                        10
% 0.93/1.02  
% 0.93/1.02  ------ Debug Options
% 0.93/1.02  
% 0.93/1.02  --dbg_backtrace                         false
% 0.93/1.02  --dbg_dump_prop_clauses                 false
% 0.93/1.02  --dbg_dump_prop_clauses_file            -
% 0.93/1.02  --dbg_out_stat                          false
% 0.93/1.02  ------ Parsing...
% 0.93/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.93/1.02  ------ Proving...
% 0.93/1.02  ------ Problem Properties 
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  clauses                                 9
% 0.93/1.02  conjectures                             2
% 0.93/1.02  EPR                                     0
% 0.93/1.02  Horn                                    9
% 0.93/1.02  unary                                   2
% 0.93/1.02  binary                                  5
% 0.93/1.02  lits                                    22
% 0.93/1.02  lits eq                                 11
% 0.93/1.02  fd_pure                                 0
% 0.93/1.02  fd_pseudo                               0
% 0.93/1.02  fd_cond                                 0
% 0.93/1.02  fd_pseudo_cond                          1
% 0.93/1.02  AC symbols                              0
% 0.93/1.02  
% 0.93/1.02  ------ Schedule dynamic 5 is on 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  ------ 
% 0.93/1.02  Current options:
% 0.93/1.02  ------ 
% 0.93/1.02  
% 0.93/1.02  ------ Input Options
% 0.93/1.02  
% 0.93/1.02  --out_options                           all
% 0.93/1.02  --tptp_safe_out                         true
% 0.93/1.02  --problem_path                          ""
% 0.93/1.02  --include_path                          ""
% 0.93/1.02  --clausifier                            res/vclausify_rel
% 0.93/1.02  --clausifier_options                    --mode clausify
% 0.93/1.02  --stdin                                 false
% 0.93/1.02  --stats_out                             all
% 0.93/1.02  
% 0.93/1.02  ------ General Options
% 0.93/1.02  
% 0.93/1.02  --fof                                   false
% 0.93/1.02  --time_out_real                         305.
% 0.93/1.02  --time_out_virtual                      -1.
% 0.93/1.02  --symbol_type_check                     false
% 0.93/1.02  --clausify_out                          false
% 0.93/1.02  --sig_cnt_out                           false
% 0.93/1.02  --trig_cnt_out                          false
% 0.93/1.02  --trig_cnt_out_tolerance                1.
% 0.93/1.02  --trig_cnt_out_sk_spl                   false
% 0.93/1.02  --abstr_cl_out                          false
% 0.93/1.02  
% 0.93/1.02  ------ Global Options
% 0.93/1.02  
% 0.93/1.02  --schedule                              default
% 0.93/1.02  --add_important_lit                     false
% 0.93/1.02  --prop_solver_per_cl                    1000
% 0.93/1.02  --min_unsat_core                        false
% 0.93/1.02  --soft_assumptions                      false
% 0.93/1.02  --soft_lemma_size                       3
% 0.93/1.02  --prop_impl_unit_size                   0
% 0.93/1.02  --prop_impl_unit                        []
% 0.93/1.02  --share_sel_clauses                     true
% 0.93/1.02  --reset_solvers                         false
% 0.93/1.02  --bc_imp_inh                            [conj_cone]
% 0.93/1.02  --conj_cone_tolerance                   3.
% 0.93/1.02  --extra_neg_conj                        none
% 0.93/1.02  --large_theory_mode                     true
% 0.93/1.02  --prolific_symb_bound                   200
% 0.93/1.02  --lt_threshold                          2000
% 0.93/1.02  --clause_weak_htbl                      true
% 0.93/1.02  --gc_record_bc_elim                     false
% 0.93/1.02  
% 0.93/1.02  ------ Preprocessing Options
% 0.93/1.02  
% 0.93/1.02  --preprocessing_flag                    true
% 0.93/1.02  --time_out_prep_mult                    0.1
% 0.93/1.02  --splitting_mode                        input
% 0.93/1.02  --splitting_grd                         true
% 0.93/1.02  --splitting_cvd                         false
% 0.93/1.02  --splitting_cvd_svl                     false
% 0.93/1.02  --splitting_nvd                         32
% 0.93/1.02  --sub_typing                            true
% 0.93/1.02  --prep_gs_sim                           true
% 0.93/1.02  --prep_unflatten                        true
% 0.93/1.02  --prep_res_sim                          true
% 0.93/1.02  --prep_upred                            true
% 0.93/1.02  --prep_sem_filter                       exhaustive
% 0.93/1.02  --prep_sem_filter_out                   false
% 0.93/1.02  --pred_elim                             true
% 0.93/1.02  --res_sim_input                         true
% 0.93/1.02  --eq_ax_congr_red                       true
% 0.93/1.02  --pure_diseq_elim                       true
% 0.93/1.02  --brand_transform                       false
% 0.93/1.02  --non_eq_to_eq                          false
% 0.93/1.02  --prep_def_merge                        true
% 0.93/1.02  --prep_def_merge_prop_impl              false
% 0.93/1.02  --prep_def_merge_mbd                    true
% 0.93/1.02  --prep_def_merge_tr_red                 false
% 0.93/1.02  --prep_def_merge_tr_cl                  false
% 0.93/1.02  --smt_preprocessing                     true
% 0.93/1.02  --smt_ac_axioms                         fast
% 0.93/1.02  --preprocessed_out                      false
% 0.93/1.02  --preprocessed_stats                    false
% 0.93/1.02  
% 0.93/1.02  ------ Abstraction refinement Options
% 0.93/1.02  
% 0.93/1.02  --abstr_ref                             []
% 0.93/1.02  --abstr_ref_prep                        false
% 0.93/1.02  --abstr_ref_until_sat                   false
% 0.93/1.02  --abstr_ref_sig_restrict                funpre
% 0.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.02  --abstr_ref_under                       []
% 0.93/1.02  
% 0.93/1.02  ------ SAT Options
% 0.93/1.02  
% 0.93/1.02  --sat_mode                              false
% 0.93/1.02  --sat_fm_restart_options                ""
% 0.93/1.02  --sat_gr_def                            false
% 0.93/1.02  --sat_epr_types                         true
% 0.93/1.02  --sat_non_cyclic_types                  false
% 0.93/1.02  --sat_finite_models                     false
% 0.93/1.02  --sat_fm_lemmas                         false
% 0.93/1.02  --sat_fm_prep                           false
% 0.93/1.02  --sat_fm_uc_incr                        true
% 0.93/1.02  --sat_out_model                         small
% 0.93/1.02  --sat_out_clauses                       false
% 0.93/1.02  
% 0.93/1.02  ------ QBF Options
% 0.93/1.02  
% 0.93/1.02  --qbf_mode                              false
% 0.93/1.02  --qbf_elim_univ                         false
% 0.93/1.02  --qbf_dom_inst                          none
% 0.93/1.02  --qbf_dom_pre_inst                      false
% 0.93/1.02  --qbf_sk_in                             false
% 0.93/1.02  --qbf_pred_elim                         true
% 0.93/1.02  --qbf_split                             512
% 0.93/1.02  
% 0.93/1.02  ------ BMC1 Options
% 0.93/1.02  
% 0.93/1.02  --bmc1_incremental                      false
% 0.93/1.02  --bmc1_axioms                           reachable_all
% 0.93/1.02  --bmc1_min_bound                        0
% 0.93/1.02  --bmc1_max_bound                        -1
% 0.93/1.02  --bmc1_max_bound_default                -1
% 0.93/1.02  --bmc1_symbol_reachability              true
% 0.93/1.02  --bmc1_property_lemmas                  false
% 0.93/1.02  --bmc1_k_induction                      false
% 0.93/1.02  --bmc1_non_equiv_states                 false
% 0.93/1.02  --bmc1_deadlock                         false
% 0.93/1.02  --bmc1_ucm                              false
% 0.93/1.02  --bmc1_add_unsat_core                   none
% 0.93/1.02  --bmc1_unsat_core_children              false
% 0.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.02  --bmc1_out_stat                         full
% 0.93/1.02  --bmc1_ground_init                      false
% 0.93/1.02  --bmc1_pre_inst_next_state              false
% 0.93/1.02  --bmc1_pre_inst_state                   false
% 0.93/1.02  --bmc1_pre_inst_reach_state             false
% 0.93/1.02  --bmc1_out_unsat_core                   false
% 0.93/1.02  --bmc1_aig_witness_out                  false
% 0.93/1.02  --bmc1_verbose                          false
% 0.93/1.02  --bmc1_dump_clauses_tptp                false
% 0.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.02  --bmc1_dump_file                        -
% 0.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.02  --bmc1_ucm_extend_mode                  1
% 0.93/1.02  --bmc1_ucm_init_mode                    2
% 0.93/1.02  --bmc1_ucm_cone_mode                    none
% 0.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.02  --bmc1_ucm_relax_model                  4
% 0.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.02  --bmc1_ucm_layered_model                none
% 0.93/1.02  --bmc1_ucm_max_lemma_size               10
% 0.93/1.02  
% 0.93/1.02  ------ AIG Options
% 0.93/1.02  
% 0.93/1.02  --aig_mode                              false
% 0.93/1.02  
% 0.93/1.02  ------ Instantiation Options
% 0.93/1.02  
% 0.93/1.02  --instantiation_flag                    true
% 0.93/1.02  --inst_sos_flag                         false
% 0.93/1.02  --inst_sos_phase                        true
% 0.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.02  --inst_lit_sel_side                     none
% 0.93/1.02  --inst_solver_per_active                1400
% 0.93/1.02  --inst_solver_calls_frac                1.
% 0.93/1.02  --inst_passive_queue_type               priority_queues
% 0.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.02  --inst_passive_queues_freq              [25;2]
% 0.93/1.02  --inst_dismatching                      true
% 0.93/1.02  --inst_eager_unprocessed_to_passive     true
% 0.93/1.02  --inst_prop_sim_given                   true
% 0.93/1.02  --inst_prop_sim_new                     false
% 0.93/1.02  --inst_subs_new                         false
% 0.93/1.02  --inst_eq_res_simp                      false
% 0.93/1.02  --inst_subs_given                       false
% 0.93/1.02  --inst_orphan_elimination               true
% 0.93/1.02  --inst_learning_loop_flag               true
% 0.93/1.02  --inst_learning_start                   3000
% 0.93/1.02  --inst_learning_factor                  2
% 0.93/1.02  --inst_start_prop_sim_after_learn       3
% 0.93/1.02  --inst_sel_renew                        solver
% 0.93/1.02  --inst_lit_activity_flag                true
% 0.93/1.02  --inst_restr_to_given                   false
% 0.93/1.02  --inst_activity_threshold               500
% 0.93/1.02  --inst_out_proof                        true
% 0.93/1.02  
% 0.93/1.02  ------ Resolution Options
% 0.93/1.02  
% 0.93/1.02  --resolution_flag                       false
% 0.93/1.02  --res_lit_sel                           adaptive
% 0.93/1.02  --res_lit_sel_side                      none
% 0.93/1.02  --res_ordering                          kbo
% 0.93/1.02  --res_to_prop_solver                    active
% 0.93/1.02  --res_prop_simpl_new                    false
% 0.93/1.02  --res_prop_simpl_given                  true
% 0.93/1.02  --res_passive_queue_type                priority_queues
% 0.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.02  --res_passive_queues_freq               [15;5]
% 0.93/1.02  --res_forward_subs                      full
% 0.93/1.02  --res_backward_subs                     full
% 0.93/1.02  --res_forward_subs_resolution           true
% 0.93/1.02  --res_backward_subs_resolution          true
% 0.93/1.02  --res_orphan_elimination                true
% 0.93/1.02  --res_time_limit                        2.
% 0.93/1.02  --res_out_proof                         true
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Options
% 0.93/1.02  
% 0.93/1.02  --superposition_flag                    true
% 0.93/1.02  --sup_passive_queue_type                priority_queues
% 0.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.02  --demod_completeness_check              fast
% 0.93/1.02  --demod_use_ground                      true
% 0.93/1.02  --sup_to_prop_solver                    passive
% 0.93/1.02  --sup_prop_simpl_new                    true
% 0.93/1.02  --sup_prop_simpl_given                  true
% 0.93/1.02  --sup_fun_splitting                     false
% 0.93/1.02  --sup_smt_interval                      50000
% 0.93/1.02  
% 0.93/1.02  ------ Superposition Simplification Setup
% 0.93/1.02  
% 0.93/1.02  --sup_indices_passive                   []
% 0.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_full_bw                           [BwDemod]
% 0.93/1.02  --sup_immed_triv                        [TrivRules]
% 0.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_immed_bw_main                     []
% 0.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.02  
% 0.93/1.02  ------ Combination Options
% 0.93/1.02  
% 0.93/1.02  --comb_res_mult                         3
% 0.93/1.02  --comb_sup_mult                         2
% 0.93/1.02  --comb_inst_mult                        10
% 0.93/1.02  
% 0.93/1.02  ------ Debug Options
% 0.93/1.02  
% 0.93/1.02  --dbg_backtrace                         false
% 0.93/1.02  --dbg_dump_prop_clauses                 false
% 0.93/1.02  --dbg_dump_prop_clauses_file            -
% 0.93/1.02  --dbg_out_stat                          false
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  ------ Proving...
% 0.93/1.02  
% 0.93/1.02  
% 0.93/1.02  % SZS status Theorem for theBenchmark.p
% 0.93/1.02  
% 0.93/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.93/1.02  
% 0.93/1.02  fof(f5,axiom,(
% 0.93/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f25,plain,(
% 0.93/1.02    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.93/1.02    inference(ennf_transformation,[],[f5])).
% 0.93/1.02  
% 0.93/1.02  fof(f26,plain,(
% 0.93/1.02    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f25])).
% 0.93/1.02  
% 0.93/1.02  fof(f50,plain,(
% 0.93/1.02    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f26])).
% 0.93/1.02  
% 0.93/1.02  fof(f8,conjecture,(
% 0.93/1.02    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f9,negated_conjecture,(
% 0.93/1.02    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 0.93/1.02    inference(negated_conjecture,[],[f8])).
% 0.93/1.02  
% 0.93/1.02  fof(f30,plain,(
% 0.93/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.93/1.02    inference(ennf_transformation,[],[f9])).
% 0.93/1.02  
% 0.93/1.02  fof(f31,plain,(
% 0.93/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f30])).
% 0.93/1.02  
% 0.93/1.02  fof(f36,plain,(
% 0.93/1.02    ( ! [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) => (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 0.93/1.02    introduced(choice_axiom,[])).
% 0.93/1.02  
% 0.93/1.02  fof(f35,plain,(
% 0.93/1.02    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.93/1.02    introduced(choice_axiom,[])).
% 0.93/1.02  
% 0.93/1.02  fof(f37,plain,(
% 0.93/1.02    (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.93/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f36,f35])).
% 0.93/1.02  
% 0.93/1.02  fof(f53,plain,(
% 0.93/1.02    ~v2_struct_0(sK0)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f56,plain,(
% 0.93/1.02    l3_lattices(sK0)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f54,plain,(
% 0.93/1.02    v10_lattices(sK0)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f1,axiom,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f12,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f1])).
% 0.93/1.02  
% 0.93/1.02  fof(f13,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f12])).
% 0.93/1.02  
% 0.93/1.02  fof(f14,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f13])).
% 0.93/1.02  
% 0.93/1.02  fof(f15,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f14])).
% 0.93/1.02  
% 0.93/1.02  fof(f16,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f15])).
% 0.93/1.02  
% 0.93/1.02  fof(f17,plain,(
% 0.93/1.02    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.93/1.02    inference(ennf_transformation,[],[f16])).
% 0.93/1.02  
% 0.93/1.02  fof(f18,plain,(
% 0.93/1.02    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.93/1.02    inference(flattening,[],[f17])).
% 0.93/1.02  
% 0.93/1.02  fof(f39,plain,(
% 0.93/1.02    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f18])).
% 0.93/1.02  
% 0.93/1.02  fof(f6,axiom,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f10,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f6])).
% 0.93/1.02  
% 0.93/1.02  fof(f27,plain,(
% 0.93/1.02    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.93/1.02    inference(ennf_transformation,[],[f10])).
% 0.93/1.02  
% 0.93/1.02  fof(f51,plain,(
% 0.93/1.02    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f27])).
% 0.93/1.02  
% 0.93/1.02  fof(f7,axiom,(
% 0.93/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f28,plain,(
% 0.93/1.02    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.93/1.02    inference(ennf_transformation,[],[f7])).
% 0.93/1.02  
% 0.93/1.02  fof(f29,plain,(
% 0.93/1.02    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f28])).
% 0.93/1.02  
% 0.93/1.02  fof(f52,plain,(
% 0.93/1.02    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f29])).
% 0.93/1.02  
% 0.93/1.02  fof(f4,axiom,(
% 0.93/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ((l3_lattices(X0) & v16_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1))))))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f23,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : ((! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.93/1.02    inference(ennf_transformation,[],[f4])).
% 0.93/1.02  
% 0.93/1.02  fof(f24,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f23])).
% 0.93/1.02  
% 0.93/1.02  fof(f34,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : (((k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1)) & (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(nnf_transformation,[],[f24])).
% 0.93/1.02  
% 0.93/1.02  fof(f48,plain,(
% 0.93/1.02    ( ! [X2,X0,X1] : (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f34])).
% 0.93/1.02  
% 0.93/1.02  fof(f59,plain,(
% 0.93/1.02    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.93/1.02    inference(equality_resolution,[],[f48])).
% 0.93/1.02  
% 0.93/1.02  fof(f2,axiom,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f11,plain,(
% 0.93/1.02    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.93/1.02    inference(pure_predicate_removal,[],[f2])).
% 0.93/1.02  
% 0.93/1.02  fof(f19,plain,(
% 0.93/1.02    ! [X0] : (((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.93/1.02    inference(ennf_transformation,[],[f11])).
% 0.93/1.02  
% 0.93/1.02  fof(f20,plain,(
% 0.93/1.02    ! [X0] : ((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.93/1.02    inference(flattening,[],[f19])).
% 0.93/1.02  
% 0.93/1.02  fof(f42,plain,(
% 0.93/1.02    ( ! [X0] : (v16_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f20])).
% 0.93/1.02  
% 0.93/1.02  fof(f55,plain,(
% 0.93/1.02    v17_lattices(sK0)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f41,plain,(
% 0.93/1.02    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f20])).
% 0.93/1.02  
% 0.93/1.02  fof(f3,axiom,(
% 0.93/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))))))),
% 0.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/1.02  
% 0.93/1.02  fof(f21,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.93/1.02    inference(ennf_transformation,[],[f3])).
% 0.93/1.02  
% 0.93/1.02  fof(f22,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f21])).
% 0.93/1.02  
% 0.93/1.02  fof(f32,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | (k2_lattices(X0,X2,X1) != k5_lattices(X0) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k1_lattices(X0,X2,X1) != k6_lattices(X0) | k1_lattices(X0,X1,X2) != k6_lattices(X0))) & ((k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(nnf_transformation,[],[f22])).
% 0.93/1.02  
% 0.93/1.02  fof(f33,plain,(
% 0.93/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | k2_lattices(X0,X2,X1) != k5_lattices(X0) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k1_lattices(X0,X2,X1) != k6_lattices(X0) | k1_lattices(X0,X1,X2) != k6_lattices(X0)) & ((k2_lattices(X0,X2,X1) = k5_lattices(X0) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k1_lattices(X0,X2,X1) = k6_lattices(X0) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.93/1.02    inference(flattening,[],[f32])).
% 0.93/1.02  
% 0.93/1.02  fof(f45,plain,(
% 0.93/1.02    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k5_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.93/1.02    inference(cnf_transformation,[],[f33])).
% 0.93/1.02  
% 0.93/1.02  fof(f58,plain,(
% 0.93/1.02    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  fof(f57,plain,(
% 0.93/1.02    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.93/1.02    inference(cnf_transformation,[],[f37])).
% 0.93/1.02  
% 0.93/1.02  cnf(c_751,plain,
% 0.93/1.02      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 0.93/1.02      theory(equality) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_999,plain,
% 0.93/1.02      ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != X0_51
% 0.93/1.02      | k5_lattices(sK0) != X0_51
% 0.93/1.02      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_751]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1077,plain,
% 0.93/1.02      ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47)
% 0.93/1.02      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
% 0.93/1.02      | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_999]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1078,plain,
% 0.93/1.02      ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
% 0.93/1.02      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
% 0.93/1.02      | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_1077]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1032,plain,
% 0.93/1.02      ( X0_51 != X1_51
% 0.93/1.02      | k5_lattices(sK0) != X1_51
% 0.93/1.02      | k5_lattices(sK0) = X0_51 ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_751]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1061,plain,
% 0.93/1.02      ( X0_51 != k5_lattices(sK0)
% 0.93/1.02      | k5_lattices(sK0) = X0_51
% 0.93/1.02      | k5_lattices(sK0) != k5_lattices(sK0) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_1032]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1067,plain,
% 0.93/1.02      ( k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) != k5_lattices(sK0)
% 0.93/1.02      | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47)
% 0.93/1.02      | k5_lattices(sK0) != k5_lattices(sK0) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_1061]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1068,plain,
% 0.93/1.02      ( k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k5_lattices(sK0)
% 0.93/1.02      | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
% 0.93/1.02      | k5_lattices(sK0) != k5_lattices(sK0) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_1067]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_748,plain,( X0_51 = X0_51 ),theory(equality) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_1031,plain,
% 0.93/1.02      ( k5_lattices(sK0) = k5_lattices(sK0) ),
% 0.93/1.02      inference(instantiation,[status(thm)],[c_748]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_12,plain,
% 0.93/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.02      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 0.93/1.02      | ~ l3_lattices(X1)
% 0.93/1.02      | v2_struct_0(X1) ),
% 0.93/1.02      inference(cnf_transformation,[],[f50]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_20,negated_conjecture,
% 0.93/1.02      ( ~ v2_struct_0(sK0) ),
% 0.93/1.02      inference(cnf_transformation,[],[f53]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_495,plain,
% 0.93/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.02      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 0.93/1.02      | ~ l3_lattices(X1)
% 0.93/1.02      | sK0 != X1 ),
% 0.93/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 0.93/1.02  
% 0.93/1.02  cnf(c_496,plain,
% 0.93/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.02      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.93/1.02      | ~ l3_lattices(sK0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_495]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_17,negated_conjecture,
% 0.93/1.03      ( l3_lattices(sK0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_500,plain,
% 0.93/1.03      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_496,c_17]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_501,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 0.93/1.03      inference(renaming,[status(thm)],[c_500]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_741,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 0.93/1.03      | m1_subset_1(k7_lattices(sK0,X0_47),u1_struct_0(sK0)) ),
% 0.93/1.03      inference(subtyping,[status(esa)],[c_501]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_917,plain,
% 0.93/1.03      ( m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 0.93/1.03      | m1_subset_1(k7_lattices(sK0,X0_47),u1_struct_0(sK0)) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_19,negated_conjecture,
% 0.93/1.03      ( v10_lattices(sK0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_0,plain,
% 0.93/1.03      ( ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0)
% 0.93/1.03      | ~ v10_lattices(X0)
% 0.93/1.03      | v6_lattices(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_13,plain,
% 0.93/1.03      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f51]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_14,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l1_lattices(X1)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | ~ v6_lattices(X1)
% 0.93/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f52]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_233,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l3_lattices(X3)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | ~ v6_lattices(X1)
% 0.93/1.03      | X1 != X3
% 0.93/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_14]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_234,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l3_lattices(X1)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | ~ v6_lattices(X1)
% 0.93/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_233]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_264,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l3_lattices(X3)
% 0.93/1.03      | ~ l3_lattices(X1)
% 0.93/1.03      | v2_struct_0(X3)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | ~ v10_lattices(X3)
% 0.93/1.03      | X1 != X3
% 0.93/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_234]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_265,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l3_lattices(X1)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | ~ v10_lattices(X1)
% 0.93/1.03      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_264]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_349,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.93/1.03      | ~ l3_lattices(X1)
% 0.93/1.03      | v2_struct_0(X1)
% 0.93/1.03      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
% 0.93/1.03      | sK0 != X1 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_265]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_350,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | ~ l3_lattices(sK0)
% 0.93/1.03      | v2_struct_0(sK0)
% 0.93/1.03      | k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_349]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_354,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_350,c_20,c_17]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_355,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0) ),
% 0.93/1.03      inference(renaming,[status(thm)],[c_354]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_742,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1_47,u1_struct_0(sK0))
% 0.93/1.03      | k4_lattices(sK0,X1_47,X0_47) = k2_lattices(sK0,X1_47,X0_47) ),
% 0.93/1.03      inference(subtyping,[status(esa)],[c_355]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_916,plain,
% 0.93/1.03      ( k4_lattices(sK0,X0_47,X1_47) = k2_lattices(sK0,X0_47,X1_47)
% 0.93/1.03      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top
% 0.93/1.03      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1015,plain,
% 0.93/1.03      ( k4_lattices(sK0,k7_lattices(sK0,X0_47),X1_47) = k2_lattices(sK0,k7_lattices(sK0,X0_47),X1_47)
% 0.93/1.03      | m1_subset_1(X0_47,u1_struct_0(sK0)) != iProver_top
% 0.93/1.03      | m1_subset_1(X1_47,u1_struct_0(sK0)) != iProver_top ),
% 0.93/1.03      inference(superposition,[status(thm)],[c_917,c_916]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_1028,plain,
% 0.93/1.03      ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
% 0.93/1.03      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_1015]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_11,plain,
% 0.93/1.03      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.93/1.03      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
% 0.93/1.03      | ~ v11_lattices(X0)
% 0.93/1.03      | ~ v16_lattices(X0)
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0)
% 0.93/1.03      | ~ v10_lattices(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f59]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_2,plain,
% 0.93/1.03      ( ~ v17_lattices(X0)
% 0.93/1.03      | v16_lattices(X0)
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_18,negated_conjecture,
% 0.93/1.03      ( v17_lattices(sK0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_218,plain,
% 0.93/1.03      ( v16_lattices(X0)
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0)
% 0.93/1.03      | sK0 != X0 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_219,plain,
% 0.93/1.03      ( v16_lattices(sK0) | ~ l3_lattices(sK0) | v2_struct_0(sK0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_218]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_57,plain,
% 0.93/1.03      ( ~ v17_lattices(sK0)
% 0.93/1.03      | v16_lattices(sK0)
% 0.93/1.03      | ~ l3_lattices(sK0)
% 0.93/1.03      | v2_struct_0(sK0) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_221,plain,
% 0.93/1.03      ( v16_lattices(sK0) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_219,c_20,c_18,c_17,c_57]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_295,plain,
% 0.93/1.03      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.93/1.03      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
% 0.93/1.03      | ~ v11_lattices(X0)
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0)
% 0.93/1.03      | ~ v10_lattices(X0)
% 0.93/1.03      | sK0 != X0 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_221]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_296,plain,
% 0.93/1.03      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.93/1.03      | ~ v11_lattices(sK0)
% 0.93/1.03      | ~ l3_lattices(sK0)
% 0.93/1.03      | v2_struct_0(sK0)
% 0.93/1.03      | ~ v10_lattices(sK0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_295]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_3,plain,
% 0.93/1.03      ( v11_lattices(X0)
% 0.93/1.03      | ~ v17_lattices(X0)
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f41]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_54,plain,
% 0.93/1.03      ( v11_lattices(sK0)
% 0.93/1.03      | ~ v17_lattices(sK0)
% 0.93/1.03      | ~ l3_lattices(sK0)
% 0.93/1.03      | v2_struct_0(sK0) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_300,plain,
% 0.93/1.03      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_296,c_20,c_19,c_18,c_17,c_54]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_543,plain,
% 0.93/1.03      ( r2_lattices(sK0,k7_lattices(sK0,X0),X0)
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 0.93/1.03      inference(backward_subsumption_resolution,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_501,c_300]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_7,plain,
% 0.93/1.03      ( ~ r2_lattices(X0,X1,X2)
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | v2_struct_0(X0)
% 0.93/1.03      | k2_lattices(X0,X1,X2) = k5_lattices(X0) ),
% 0.93/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_418,plain,
% 0.93/1.03      ( ~ r2_lattices(X0,X1,X2)
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.93/1.03      | ~ l3_lattices(X0)
% 0.93/1.03      | k2_lattices(X0,X1,X2) = k5_lattices(X0)
% 0.93/1.03      | sK0 != X0 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_419,plain,
% 0.93/1.03      ( ~ r2_lattices(sK0,X0,X1)
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | ~ l3_lattices(sK0)
% 0.93/1.03      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_418]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_423,plain,
% 0.93/1.03      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ r2_lattices(sK0,X0,X1)
% 0.93/1.03      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_419,c_17]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_424,plain,
% 0.93/1.03      ( ~ r2_lattices(sK0,X0,X1)
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | k2_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
% 0.93/1.03      inference(renaming,[status(thm)],[c_423]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_596,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK0))
% 0.93/1.03      | X2 != X1
% 0.93/1.03      | k2_lattices(sK0,X0,X2) = k5_lattices(sK0)
% 0.93/1.03      | k7_lattices(sK0,X1) != X0
% 0.93/1.03      | sK0 != sK0 ),
% 0.93/1.03      inference(resolution_lifted,[status(thm)],[c_543,c_424]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_597,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 0.93/1.03      | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
% 0.93/1.03      inference(unflattening,[status(thm)],[c_596]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_601,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 0.93/1.03      | k2_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
% 0.93/1.03      inference(global_propositional_subsumption,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_597,c_17,c_496]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_738,plain,
% 0.93/1.03      ( ~ m1_subset_1(X0_47,u1_struct_0(sK0))
% 0.93/1.03      | k2_lattices(sK0,k7_lattices(sK0,X0_47),X0_47) = k5_lattices(sK0) ),
% 0.93/1.03      inference(subtyping,[status(esa)],[c_601]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_780,plain,
% 0.93/1.03      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 0.93/1.03      | k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
% 0.93/1.03      inference(instantiation,[status(thm)],[c_738]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_15,negated_conjecture,
% 0.93/1.03      ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
% 0.93/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_744,negated_conjecture,
% 0.93/1.03      ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
% 0.93/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_16,negated_conjecture,
% 0.93/1.03      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 0.93/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(c_25,plain,
% 0.93/1.03      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 0.93/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.93/1.03  
% 0.93/1.03  cnf(contradiction,plain,
% 0.93/1.03      ( $false ),
% 0.93/1.03      inference(minisat,
% 0.93/1.03                [status(thm)],
% 0.93/1.03                [c_1078,c_1068,c_1031,c_1028,c_780,c_744,c_25,c_16]) ).
% 0.93/1.03  
% 0.93/1.03  
% 0.93/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.93/1.03  
% 0.93/1.03  ------                               Statistics
% 0.93/1.03  
% 0.93/1.03  ------ General
% 0.93/1.03  
% 0.93/1.03  abstr_ref_over_cycles:                  0
% 0.93/1.03  abstr_ref_under_cycles:                 0
% 0.93/1.03  gc_basic_clause_elim:                   0
% 0.93/1.03  forced_gc_time:                         0
% 0.93/1.03  parsing_time:                           0.009
% 0.93/1.03  unif_index_cands_time:                  0.
% 0.93/1.03  unif_index_add_time:                    0.
% 0.93/1.03  orderings_time:                         0.
% 0.93/1.03  out_proof_time:                         0.007
% 0.93/1.03  total_time:                             0.058
% 0.93/1.03  num_of_symbols:                         52
% 0.93/1.03  num_of_terms:                           775
% 0.93/1.03  
% 0.93/1.03  ------ Preprocessing
% 0.93/1.03  
% 0.93/1.03  num_of_splits:                          0
% 0.93/1.03  num_of_split_atoms:                     0
% 0.93/1.03  num_of_reused_defs:                     0
% 0.93/1.03  num_eq_ax_congr_red:                    21
% 0.93/1.03  num_of_sem_filtered_clauses:            1
% 0.93/1.03  num_of_subtypes:                        5
% 0.93/1.03  monotx_restored_types:                  0
% 0.93/1.03  sat_num_of_epr_types:                   0
% 0.93/1.03  sat_num_of_non_cyclic_types:            0
% 0.93/1.03  sat_guarded_non_collapsed_types:        1
% 0.93/1.03  num_pure_diseq_elim:                    0
% 0.93/1.03  simp_replaced_by:                       0
% 0.93/1.03  res_preprocessed:                       69
% 0.93/1.03  prep_upred:                             0
% 0.93/1.03  prep_unflattend:                        23
% 0.93/1.03  smt_new_axioms:                         0
% 0.93/1.03  pred_elim_cands:                        1
% 0.93/1.03  pred_elim:                              9
% 0.93/1.03  pred_elim_cl:                           10
% 0.93/1.03  pred_elim_cycles:                       11
% 0.93/1.03  merged_defs:                            0
% 0.93/1.03  merged_defs_ncl:                        0
% 0.93/1.03  bin_hyper_res:                          0
% 0.93/1.03  prep_cycles:                            4
% 0.93/1.03  pred_elim_time:                         0.006
% 0.93/1.03  splitting_time:                         0.
% 0.93/1.03  sem_filter_time:                        0.
% 0.93/1.03  monotx_time:                            0.
% 0.93/1.03  subtype_inf_time:                       0.
% 0.93/1.03  
% 0.93/1.03  ------ Problem properties
% 0.93/1.03  
% 0.93/1.03  clauses:                                9
% 0.93/1.03  conjectures:                            2
% 0.93/1.03  epr:                                    0
% 0.93/1.03  horn:                                   9
% 0.93/1.03  ground:                                 2
% 0.93/1.03  unary:                                  2
% 0.93/1.03  binary:                                 5
% 0.93/1.03  lits:                                   22
% 0.93/1.03  lits_eq:                                11
% 0.93/1.03  fd_pure:                                0
% 0.93/1.03  fd_pseudo:                              0
% 0.93/1.03  fd_cond:                                0
% 0.93/1.03  fd_pseudo_cond:                         1
% 0.93/1.03  ac_symbols:                             0
% 0.93/1.03  
% 0.93/1.03  ------ Propositional Solver
% 0.93/1.03  
% 0.93/1.03  prop_solver_calls:                      25
% 0.93/1.03  prop_fast_solver_calls:                 541
% 0.93/1.03  smt_solver_calls:                       0
% 0.93/1.03  smt_fast_solver_calls:                  0
% 0.93/1.03  prop_num_of_clauses:                    274
% 0.93/1.03  prop_preprocess_simplified:             1802
% 0.93/1.03  prop_fo_subsumed:                       24
% 0.93/1.03  prop_solver_time:                       0.
% 0.93/1.03  smt_solver_time:                        0.
% 0.93/1.03  smt_fast_solver_time:                   0.
% 0.93/1.03  prop_fast_solver_time:                  0.
% 0.93/1.03  prop_unsat_core_time:                   0.
% 0.93/1.03  
% 0.93/1.03  ------ QBF
% 0.93/1.03  
% 0.93/1.03  qbf_q_res:                              0
% 0.93/1.03  qbf_num_tautologies:                    0
% 0.93/1.03  qbf_prep_cycles:                        0
% 0.93/1.03  
% 0.93/1.03  ------ BMC1
% 0.93/1.03  
% 0.93/1.03  bmc1_current_bound:                     -1
% 0.93/1.03  bmc1_last_solved_bound:                 -1
% 0.93/1.03  bmc1_unsat_core_size:                   -1
% 0.93/1.03  bmc1_unsat_core_parents_size:           -1
% 0.93/1.03  bmc1_merge_next_fun:                    0
% 0.93/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.93/1.03  
% 0.93/1.03  ------ Instantiation
% 0.93/1.03  
% 0.93/1.03  inst_num_of_clauses:                    35
% 0.93/1.03  inst_num_in_passive:                    2
% 0.93/1.03  inst_num_in_active:                     32
% 0.93/1.03  inst_num_in_unprocessed:                0
% 0.93/1.03  inst_num_of_loops:                      37
% 0.93/1.03  inst_num_of_learning_restarts:          0
% 0.93/1.03  inst_num_moves_active_passive:          0
% 0.93/1.03  inst_lit_activity:                      0
% 0.93/1.03  inst_lit_activity_moves:                0
% 0.93/1.03  inst_num_tautologies:                   0
% 0.93/1.03  inst_num_prop_implied:                  0
% 0.93/1.03  inst_num_existing_simplified:           0
% 0.93/1.03  inst_num_eq_res_simplified:             0
% 0.93/1.03  inst_num_child_elim:                    0
% 0.93/1.03  inst_num_of_dismatching_blockings:      0
% 0.93/1.03  inst_num_of_non_proper_insts:           20
% 0.93/1.03  inst_num_of_duplicates:                 0
% 0.93/1.03  inst_inst_num_from_inst_to_res:         0
% 0.93/1.03  inst_dismatching_checking_time:         0.
% 0.93/1.03  
% 0.93/1.03  ------ Resolution
% 0.93/1.03  
% 0.93/1.03  res_num_of_clauses:                     0
% 0.93/1.03  res_num_in_passive:                     0
% 0.93/1.03  res_num_in_active:                      0
% 0.93/1.03  res_num_of_loops:                       73
% 0.93/1.03  res_forward_subset_subsumed:            2
% 0.93/1.03  res_backward_subset_subsumed:           0
% 0.93/1.03  res_forward_subsumed:                   0
% 0.93/1.03  res_backward_subsumed:                  0
% 0.93/1.03  res_forward_subsumption_resolution:     0
% 0.93/1.03  res_backward_subsumption_resolution:    1
% 0.93/1.03  res_clause_to_clause_subsumption:       37
% 0.93/1.03  res_orphan_elimination:                 0
% 0.93/1.03  res_tautology_del:                      11
% 0.93/1.03  res_num_eq_res_simplified:              0
% 0.93/1.03  res_num_sel_changes:                    0
% 0.93/1.03  res_moves_from_active_to_pass:          0
% 0.93/1.03  
% 0.93/1.03  ------ Superposition
% 0.93/1.03  
% 0.93/1.03  sup_time_total:                         0.
% 0.93/1.03  sup_time_generating:                    0.
% 0.93/1.03  sup_time_sim_full:                      0.
% 0.93/1.03  sup_time_sim_immed:                     0.
% 0.93/1.03  
% 0.93/1.03  sup_num_of_clauses:                     13
% 0.93/1.03  sup_num_in_active:                      6
% 0.93/1.03  sup_num_in_passive:                     7
% 0.93/1.03  sup_num_of_loops:                       6
% 0.93/1.03  sup_fw_superposition:                   4
% 0.93/1.03  sup_bw_superposition:                   0
% 0.93/1.03  sup_immediate_simplified:               0
% 0.93/1.03  sup_given_eliminated:                   0
% 0.93/1.03  comparisons_done:                       0
% 0.93/1.03  comparisons_avoided:                    0
% 0.93/1.03  
% 0.93/1.03  ------ Simplifications
% 0.93/1.03  
% 0.93/1.03  
% 0.93/1.03  sim_fw_subset_subsumed:                 0
% 0.93/1.03  sim_bw_subset_subsumed:                 0
% 0.93/1.03  sim_fw_subsumed:                        0
% 0.93/1.03  sim_bw_subsumed:                        0
% 0.93/1.03  sim_fw_subsumption_res:                 0
% 0.93/1.03  sim_bw_subsumption_res:                 0
% 0.93/1.03  sim_tautology_del:                      0
% 0.93/1.03  sim_eq_tautology_del:                   0
% 0.93/1.03  sim_eq_res_simp:                        0
% 0.93/1.03  sim_fw_demodulated:                     0
% 0.93/1.03  sim_bw_demodulated:                     0
% 0.93/1.03  sim_light_normalised:                   0
% 0.93/1.03  sim_joinable_taut:                      0
% 0.93/1.03  sim_joinable_simp:                      0
% 0.93/1.03  sim_ac_normalised:                      0
% 0.93/1.03  sim_smt_subsumption:                    0
% 0.93/1.03  
%------------------------------------------------------------------------------
