%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:22 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 410 expanded)
%              Number of clauses        :   82 ( 126 expanded)
%              Number of leaves         :   14 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  467 (2183 expanded)
%              Number of equality atoms :  133 ( 459 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,sK2)) != k7_lattices(X0,k3_lattices(X0,X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k4_lattices(X0,k7_lattices(X0,sK1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,sK1,X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X2)) != k7_lattices(sK0,k3_lattices(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f41,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    l3_lattices(sK0) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
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
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_350,plain,
    ( X0_42 != X1_42
    | k7_lattices(X0_44,X0_42) = k7_lattices(X0_44,X1_42) ),
    theory(equality)).

cnf(c_493,plain,
    ( k3_lattices(sK0,sK1,sK2) != X0_42
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,X0_42) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_502,plain,
    ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,X0_42,X1_42)
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,X1_42)) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_995,plain,
    ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_15362,plain,
    ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_13,c_12,c_10])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42)) = k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_4162,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,X0_42,k7_lattices(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_12459,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_4162])).

cnf(c_347,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_707,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != X0_42
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X1_42,sK2))
    | k7_lattices(sK0,k3_lattices(sK0,X1_42,sK2)) != X0_42 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_11315,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | k7_lattices(sK0,k3_lattices(sK0,X0_42,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_11316,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_11315])).

cnf(c_351,plain,
    ( X0_42 != X1_42
    | X2_42 != X3_42
    | k3_lattices(X0_44,X0_42,X2_42) = k3_lattices(X0_44,X1_42,X3_42) ),
    theory(equality)).

cnf(c_520,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,X0_42,X1_42)
    | sK2 != X1_42
    | sK1 != X0_42 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_987,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | sK1 != X0_42 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_4398,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | sK1 != k7_lattices(sK0,X0_42) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_7121,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,X0_42)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | sK1 != k7_lattices(sK0,k7_lattices(sK0,X0_42)) ),
    inference(instantiation,[status(thm)],[c_4398])).

cnf(c_7123,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7121])).

cnf(c_1120,plain,
    ( X0_42 != X1_42
    | X0_42 = k7_lattices(sK0,X2_42)
    | k7_lattices(sK0,X2_42) != X1_42 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_1629,plain,
    ( X0_42 != k7_lattices(sK0,X1_42)
    | X0_42 = k7_lattices(sK0,X2_42)
    | k7_lattices(sK0,X2_42) != k7_lattices(sK0,X1_42) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1776,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,X0_42)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
    | k7_lattices(sK0,X0_42) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_5453,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
    | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_2483,plain,
    ( X0_42 != k7_lattices(sK0,X1_42)
    | k7_lattices(sK0,X0_42) = k7_lattices(sK0,k7_lattices(sK0,X1_42)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_4694,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42)) != k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42))
    | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42))) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42))) ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_5452,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) != k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_4694])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v6_lattices(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_138,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_139])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_12])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_13,c_10])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0_42,X1_42),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_251])).

cnf(c_2233,plain,
    ( m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_276,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_10])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_42),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_2206,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_1615,plain,
    ( X0_42 != X1_42
    | X0_42 = k7_lattices(sK0,k7_lattices(sK0,X1_42))
    | k7_lattices(sK0,k7_lattices(sK0,X1_42)) != X1_42 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1616,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1
    | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k7_lattices(X1,k7_lattices(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_13,c_12,c_10])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_1425,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_818,plain,
    ( X0_42 != X1_42
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != X1_42
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = X0_42 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_1041,plain,
    ( X0_42 != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = X0_42
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1424,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
    | k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_346,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_1038,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_559,plain,
    ( X0_42 != X1_42
    | sK2 != X1_42
    | sK2 = X0_42 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_639,plain,
    ( X0_42 != sK2
    | sK2 = X0_42
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_852,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK2)) != sK2
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_729,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_343,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_466,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_469,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,X0_42)) = X0_42
    | m1_subset_1(X0_42,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_524,plain,
    ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_466,c_469])).

cnf(c_370,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_364,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_7,negated_conjecture,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_344,negated_conjecture,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_357,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15362,c_12459,c_11316,c_7123,c_5453,c_5452,c_2233,c_2206,c_1616,c_1425,c_1424,c_1038,c_852,c_729,c_524,c_370,c_364,c_344,c_357,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:50:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.79/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.98  
% 3.79/0.98  ------  iProver source info
% 3.79/0.98  
% 3.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.98  git: non_committed_changes: false
% 3.79/0.98  git: last_make_outside_of_git: false
% 3.79/0.98  
% 3.79/0.98  ------ 
% 3.79/0.98  
% 3.79/0.98  ------ Input Options
% 3.79/0.98  
% 3.79/0.98  --out_options                           all
% 3.79/0.98  --tptp_safe_out                         true
% 3.79/0.98  --problem_path                          ""
% 3.79/0.98  --include_path                          ""
% 3.79/0.98  --clausifier                            res/vclausify_rel
% 3.79/0.98  --clausifier_options                    ""
% 3.79/0.98  --stdin                                 false
% 3.79/0.98  --stats_out                             all
% 3.79/0.98  
% 3.79/0.98  ------ General Options
% 3.79/0.98  
% 3.79/0.98  --fof                                   false
% 3.79/0.98  --time_out_real                         305.
% 3.79/0.98  --time_out_virtual                      -1.
% 3.79/0.98  --symbol_type_check                     false
% 3.79/0.98  --clausify_out                          false
% 3.79/0.98  --sig_cnt_out                           false
% 3.79/0.98  --trig_cnt_out                          false
% 3.79/0.98  --trig_cnt_out_tolerance                1.
% 3.79/0.98  --trig_cnt_out_sk_spl                   false
% 3.79/0.98  --abstr_cl_out                          false
% 3.79/0.98  
% 3.79/0.98  ------ Global Options
% 3.79/0.98  
% 3.79/0.98  --schedule                              default
% 3.79/0.98  --add_important_lit                     false
% 3.79/0.98  --prop_solver_per_cl                    1000
% 3.79/0.98  --min_unsat_core                        false
% 3.79/0.98  --soft_assumptions                      false
% 3.79/0.98  --soft_lemma_size                       3
% 3.79/0.98  --prop_impl_unit_size                   0
% 3.79/0.98  --prop_impl_unit                        []
% 3.79/0.98  --share_sel_clauses                     true
% 3.79/0.98  --reset_solvers                         false
% 3.79/0.98  --bc_imp_inh                            [conj_cone]
% 3.79/0.98  --conj_cone_tolerance                   3.
% 3.79/0.98  --extra_neg_conj                        none
% 3.79/0.98  --large_theory_mode                     true
% 3.79/0.98  --prolific_symb_bound                   200
% 3.79/0.98  --lt_threshold                          2000
% 3.79/0.98  --clause_weak_htbl                      true
% 3.79/0.98  --gc_record_bc_elim                     false
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing Options
% 3.79/0.98  
% 3.79/0.98  --preprocessing_flag                    true
% 3.79/0.98  --time_out_prep_mult                    0.1
% 3.79/0.98  --splitting_mode                        input
% 3.79/0.98  --splitting_grd                         true
% 3.79/0.98  --splitting_cvd                         false
% 3.79/0.98  --splitting_cvd_svl                     false
% 3.79/0.98  --splitting_nvd                         32
% 3.79/0.98  --sub_typing                            true
% 3.79/0.98  --prep_gs_sim                           true
% 3.79/0.98  --prep_unflatten                        true
% 3.79/0.98  --prep_res_sim                          true
% 3.79/0.98  --prep_upred                            true
% 3.79/0.98  --prep_sem_filter                       exhaustive
% 3.79/0.98  --prep_sem_filter_out                   false
% 3.79/0.98  --pred_elim                             true
% 3.79/0.98  --res_sim_input                         true
% 3.79/0.98  --eq_ax_congr_red                       true
% 3.79/0.98  --pure_diseq_elim                       true
% 3.79/0.98  --brand_transform                       false
% 3.79/0.98  --non_eq_to_eq                          false
% 3.79/0.98  --prep_def_merge                        true
% 3.79/0.98  --prep_def_merge_prop_impl              false
% 3.79/0.98  --prep_def_merge_mbd                    true
% 3.79/0.98  --prep_def_merge_tr_red                 false
% 3.79/0.98  --prep_def_merge_tr_cl                  false
% 3.79/0.98  --smt_preprocessing                     true
% 3.79/0.98  --smt_ac_axioms                         fast
% 3.79/0.98  --preprocessed_out                      false
% 3.79/0.98  --preprocessed_stats                    false
% 3.79/0.98  
% 3.79/0.98  ------ Abstraction refinement Options
% 3.79/0.98  
% 3.79/0.98  --abstr_ref                             []
% 3.79/0.98  --abstr_ref_prep                        false
% 3.79/0.98  --abstr_ref_until_sat                   false
% 3.79/0.98  --abstr_ref_sig_restrict                funpre
% 3.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.98  --abstr_ref_under                       []
% 3.79/0.98  
% 3.79/0.98  ------ SAT Options
% 3.79/0.98  
% 3.79/0.98  --sat_mode                              false
% 3.79/0.98  --sat_fm_restart_options                ""
% 3.79/0.98  --sat_gr_def                            false
% 3.79/0.98  --sat_epr_types                         true
% 3.79/0.98  --sat_non_cyclic_types                  false
% 3.79/0.98  --sat_finite_models                     false
% 3.79/0.98  --sat_fm_lemmas                         false
% 3.79/0.98  --sat_fm_prep                           false
% 3.79/0.98  --sat_fm_uc_incr                        true
% 3.79/0.98  --sat_out_model                         small
% 3.79/0.98  --sat_out_clauses                       false
% 3.79/0.98  
% 3.79/0.98  ------ QBF Options
% 3.79/0.98  
% 3.79/0.98  --qbf_mode                              false
% 3.79/0.98  --qbf_elim_univ                         false
% 3.79/0.98  --qbf_dom_inst                          none
% 3.79/0.98  --qbf_dom_pre_inst                      false
% 3.79/0.98  --qbf_sk_in                             false
% 3.79/0.98  --qbf_pred_elim                         true
% 3.79/0.98  --qbf_split                             512
% 3.79/0.98  
% 3.79/0.98  ------ BMC1 Options
% 3.79/0.98  
% 3.79/0.98  --bmc1_incremental                      false
% 3.79/0.98  --bmc1_axioms                           reachable_all
% 3.79/0.98  --bmc1_min_bound                        0
% 3.79/0.98  --bmc1_max_bound                        -1
% 3.79/0.98  --bmc1_max_bound_default                -1
% 3.79/0.98  --bmc1_symbol_reachability              true
% 3.79/0.98  --bmc1_property_lemmas                  false
% 3.79/0.98  --bmc1_k_induction                      false
% 3.79/0.98  --bmc1_non_equiv_states                 false
% 3.79/0.98  --bmc1_deadlock                         false
% 3.79/0.98  --bmc1_ucm                              false
% 3.79/0.98  --bmc1_add_unsat_core                   none
% 3.79/0.98  --bmc1_unsat_core_children              false
% 3.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.98  --bmc1_out_stat                         full
% 3.79/0.98  --bmc1_ground_init                      false
% 3.79/0.98  --bmc1_pre_inst_next_state              false
% 3.79/0.98  --bmc1_pre_inst_state                   false
% 3.79/0.98  --bmc1_pre_inst_reach_state             false
% 3.79/0.98  --bmc1_out_unsat_core                   false
% 3.79/0.98  --bmc1_aig_witness_out                  false
% 3.79/0.98  --bmc1_verbose                          false
% 3.79/0.98  --bmc1_dump_clauses_tptp                false
% 3.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.98  --bmc1_dump_file                        -
% 3.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.98  --bmc1_ucm_extend_mode                  1
% 3.79/0.98  --bmc1_ucm_init_mode                    2
% 3.79/0.98  --bmc1_ucm_cone_mode                    none
% 3.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.98  --bmc1_ucm_relax_model                  4
% 3.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.98  --bmc1_ucm_layered_model                none
% 3.79/0.98  --bmc1_ucm_max_lemma_size               10
% 3.79/0.98  
% 3.79/0.98  ------ AIG Options
% 3.79/0.98  
% 3.79/0.98  --aig_mode                              false
% 3.79/0.98  
% 3.79/0.98  ------ Instantiation Options
% 3.79/0.98  
% 3.79/0.98  --instantiation_flag                    true
% 3.79/0.98  --inst_sos_flag                         true
% 3.79/0.98  --inst_sos_phase                        true
% 3.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.98  --inst_lit_sel_side                     num_symb
% 3.79/0.98  --inst_solver_per_active                1400
% 3.79/0.98  --inst_solver_calls_frac                1.
% 3.79/0.98  --inst_passive_queue_type               priority_queues
% 3.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.98  --inst_passive_queues_freq              [25;2]
% 3.79/0.98  --inst_dismatching                      true
% 3.79/0.98  --inst_eager_unprocessed_to_passive     true
% 3.79/0.98  --inst_prop_sim_given                   true
% 3.79/0.98  --inst_prop_sim_new                     false
% 3.79/0.98  --inst_subs_new                         false
% 3.79/0.98  --inst_eq_res_simp                      false
% 3.79/0.98  --inst_subs_given                       false
% 3.79/0.98  --inst_orphan_elimination               true
% 3.79/0.98  --inst_learning_loop_flag               true
% 3.79/0.98  --inst_learning_start                   3000
% 3.79/0.98  --inst_learning_factor                  2
% 3.79/0.98  --inst_start_prop_sim_after_learn       3
% 3.79/0.98  --inst_sel_renew                        solver
% 3.79/0.98  --inst_lit_activity_flag                true
% 3.79/0.98  --inst_restr_to_given                   false
% 3.79/0.98  --inst_activity_threshold               500
% 3.79/0.98  --inst_out_proof                        true
% 3.79/0.98  
% 3.79/0.98  ------ Resolution Options
% 3.79/0.98  
% 3.79/0.98  --resolution_flag                       true
% 3.79/0.98  --res_lit_sel                           adaptive
% 3.79/0.98  --res_lit_sel_side                      none
% 3.79/0.98  --res_ordering                          kbo
% 3.79/0.98  --res_to_prop_solver                    active
% 3.79/0.98  --res_prop_simpl_new                    false
% 3.79/0.98  --res_prop_simpl_given                  true
% 3.79/0.98  --res_passive_queue_type                priority_queues
% 3.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.98  --res_passive_queues_freq               [15;5]
% 3.79/0.98  --res_forward_subs                      full
% 3.79/0.98  --res_backward_subs                     full
% 3.79/0.98  --res_forward_subs_resolution           true
% 3.79/0.98  --res_backward_subs_resolution          true
% 3.79/0.98  --res_orphan_elimination                true
% 3.79/0.98  --res_time_limit                        2.
% 3.79/0.98  --res_out_proof                         true
% 3.79/0.98  
% 3.79/0.98  ------ Superposition Options
% 3.79/0.98  
% 3.79/0.98  --superposition_flag                    true
% 3.79/0.98  --sup_passive_queue_type                priority_queues
% 3.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.98  --demod_completeness_check              fast
% 3.79/0.98  --demod_use_ground                      true
% 3.79/0.98  --sup_to_prop_solver                    passive
% 3.79/0.98  --sup_prop_simpl_new                    true
% 3.79/0.98  --sup_prop_simpl_given                  true
% 3.79/0.98  --sup_fun_splitting                     true
% 3.79/0.98  --sup_smt_interval                      50000
% 3.79/0.98  
% 3.79/0.98  ------ Superposition Simplification Setup
% 3.79/0.98  
% 3.79/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.98  --sup_immed_triv                        [TrivRules]
% 3.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_immed_bw_main                     []
% 3.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_input_bw                          []
% 3.79/0.98  
% 3.79/0.98  ------ Combination Options
% 3.79/0.98  
% 3.79/0.98  --comb_res_mult                         3
% 3.79/0.98  --comb_sup_mult                         2
% 3.79/0.98  --comb_inst_mult                        10
% 3.79/0.98  
% 3.79/0.98  ------ Debug Options
% 3.79/0.98  
% 3.79/0.98  --dbg_backtrace                         false
% 3.79/0.98  --dbg_dump_prop_clauses                 false
% 3.79/0.98  --dbg_dump_prop_clauses_file            -
% 3.79/0.98  --dbg_out_stat                          false
% 3.79/0.98  ------ Parsing...
% 3.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.98  ------ Proving...
% 3.79/0.98  ------ Problem Properties 
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  clauses                                 7
% 3.79/0.98  conjectures                             3
% 3.79/0.98  EPR                                     0
% 3.79/0.98  Horn                                    7
% 3.79/0.98  unary                                   3
% 3.79/0.98  binary                                  2
% 3.79/0.98  lits                                    13
% 3.79/0.98  lits eq                                 3
% 3.79/0.98  fd_pure                                 0
% 3.79/0.98  fd_pseudo                               0
% 3.79/0.98  fd_cond                                 0
% 3.79/0.98  fd_pseudo_cond                          0
% 3.79/0.98  AC symbols                              0
% 3.79/0.98  
% 3.79/0.98  ------ Schedule dynamic 5 is on 
% 3.79/0.98  
% 3.79/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  ------ 
% 3.79/0.98  Current options:
% 3.79/0.98  ------ 
% 3.79/0.98  
% 3.79/0.98  ------ Input Options
% 3.79/0.98  
% 3.79/0.98  --out_options                           all
% 3.79/0.98  --tptp_safe_out                         true
% 3.79/0.98  --problem_path                          ""
% 3.79/0.98  --include_path                          ""
% 3.79/0.98  --clausifier                            res/vclausify_rel
% 3.79/0.98  --clausifier_options                    ""
% 3.79/0.98  --stdin                                 false
% 3.79/0.98  --stats_out                             all
% 3.79/0.98  
% 3.79/0.98  ------ General Options
% 3.79/0.98  
% 3.79/0.98  --fof                                   false
% 3.79/0.98  --time_out_real                         305.
% 3.79/0.98  --time_out_virtual                      -1.
% 3.79/0.98  --symbol_type_check                     false
% 3.79/0.98  --clausify_out                          false
% 3.79/0.98  --sig_cnt_out                           false
% 3.79/0.98  --trig_cnt_out                          false
% 3.79/0.98  --trig_cnt_out_tolerance                1.
% 3.79/0.98  --trig_cnt_out_sk_spl                   false
% 3.79/0.98  --abstr_cl_out                          false
% 3.79/0.98  
% 3.79/0.98  ------ Global Options
% 3.79/0.98  
% 3.79/0.98  --schedule                              default
% 3.79/0.98  --add_important_lit                     false
% 3.79/0.98  --prop_solver_per_cl                    1000
% 3.79/0.98  --min_unsat_core                        false
% 3.79/0.98  --soft_assumptions                      false
% 3.79/0.98  --soft_lemma_size                       3
% 3.79/0.98  --prop_impl_unit_size                   0
% 3.79/0.98  --prop_impl_unit                        []
% 3.79/0.98  --share_sel_clauses                     true
% 3.79/0.98  --reset_solvers                         false
% 3.79/0.98  --bc_imp_inh                            [conj_cone]
% 3.79/0.98  --conj_cone_tolerance                   3.
% 3.79/0.98  --extra_neg_conj                        none
% 3.79/0.98  --large_theory_mode                     true
% 3.79/0.98  --prolific_symb_bound                   200
% 3.79/0.98  --lt_threshold                          2000
% 3.79/0.98  --clause_weak_htbl                      true
% 3.79/0.98  --gc_record_bc_elim                     false
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing Options
% 3.79/0.98  
% 3.79/0.98  --preprocessing_flag                    true
% 3.79/0.98  --time_out_prep_mult                    0.1
% 3.79/0.98  --splitting_mode                        input
% 3.79/0.98  --splitting_grd                         true
% 3.79/0.98  --splitting_cvd                         false
% 3.79/0.98  --splitting_cvd_svl                     false
% 3.79/0.98  --splitting_nvd                         32
% 3.79/0.98  --sub_typing                            true
% 3.79/0.98  --prep_gs_sim                           true
% 3.79/0.98  --prep_unflatten                        true
% 3.79/0.98  --prep_res_sim                          true
% 3.79/0.98  --prep_upred                            true
% 3.79/0.98  --prep_sem_filter                       exhaustive
% 3.79/0.98  --prep_sem_filter_out                   false
% 3.79/0.98  --pred_elim                             true
% 3.79/0.98  --res_sim_input                         true
% 3.79/0.98  --eq_ax_congr_red                       true
% 3.79/0.98  --pure_diseq_elim                       true
% 3.79/0.98  --brand_transform                       false
% 3.79/0.98  --non_eq_to_eq                          false
% 3.79/0.98  --prep_def_merge                        true
% 3.79/0.98  --prep_def_merge_prop_impl              false
% 3.79/0.98  --prep_def_merge_mbd                    true
% 3.79/0.98  --prep_def_merge_tr_red                 false
% 3.79/0.98  --prep_def_merge_tr_cl                  false
% 3.79/0.98  --smt_preprocessing                     true
% 3.79/0.98  --smt_ac_axioms                         fast
% 3.79/0.98  --preprocessed_out                      false
% 3.79/0.98  --preprocessed_stats                    false
% 3.79/0.98  
% 3.79/0.98  ------ Abstraction refinement Options
% 3.79/0.98  
% 3.79/0.98  --abstr_ref                             []
% 3.79/0.98  --abstr_ref_prep                        false
% 3.79/0.98  --abstr_ref_until_sat                   false
% 3.79/0.98  --abstr_ref_sig_restrict                funpre
% 3.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.98  --abstr_ref_under                       []
% 3.79/0.98  
% 3.79/0.98  ------ SAT Options
% 3.79/0.98  
% 3.79/0.98  --sat_mode                              false
% 3.79/0.98  --sat_fm_restart_options                ""
% 3.79/0.98  --sat_gr_def                            false
% 3.79/0.98  --sat_epr_types                         true
% 3.79/0.98  --sat_non_cyclic_types                  false
% 3.79/0.98  --sat_finite_models                     false
% 3.79/0.98  --sat_fm_lemmas                         false
% 3.79/0.98  --sat_fm_prep                           false
% 3.79/0.98  --sat_fm_uc_incr                        true
% 3.79/0.98  --sat_out_model                         small
% 3.79/0.98  --sat_out_clauses                       false
% 3.79/0.98  
% 3.79/0.98  ------ QBF Options
% 3.79/0.98  
% 3.79/0.98  --qbf_mode                              false
% 3.79/0.98  --qbf_elim_univ                         false
% 3.79/0.98  --qbf_dom_inst                          none
% 3.79/0.98  --qbf_dom_pre_inst                      false
% 3.79/0.98  --qbf_sk_in                             false
% 3.79/0.98  --qbf_pred_elim                         true
% 3.79/0.98  --qbf_split                             512
% 3.79/0.98  
% 3.79/0.98  ------ BMC1 Options
% 3.79/0.98  
% 3.79/0.98  --bmc1_incremental                      false
% 3.79/0.98  --bmc1_axioms                           reachable_all
% 3.79/0.98  --bmc1_min_bound                        0
% 3.79/0.98  --bmc1_max_bound                        -1
% 3.79/0.98  --bmc1_max_bound_default                -1
% 3.79/0.98  --bmc1_symbol_reachability              true
% 3.79/0.98  --bmc1_property_lemmas                  false
% 3.79/0.98  --bmc1_k_induction                      false
% 3.79/0.98  --bmc1_non_equiv_states                 false
% 3.79/0.98  --bmc1_deadlock                         false
% 3.79/0.98  --bmc1_ucm                              false
% 3.79/0.98  --bmc1_add_unsat_core                   none
% 3.79/0.98  --bmc1_unsat_core_children              false
% 3.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.98  --bmc1_out_stat                         full
% 3.79/0.98  --bmc1_ground_init                      false
% 3.79/0.98  --bmc1_pre_inst_next_state              false
% 3.79/0.98  --bmc1_pre_inst_state                   false
% 3.79/0.98  --bmc1_pre_inst_reach_state             false
% 3.79/0.98  --bmc1_out_unsat_core                   false
% 3.79/0.98  --bmc1_aig_witness_out                  false
% 3.79/0.98  --bmc1_verbose                          false
% 3.79/0.98  --bmc1_dump_clauses_tptp                false
% 3.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.98  --bmc1_dump_file                        -
% 3.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.98  --bmc1_ucm_extend_mode                  1
% 3.79/0.98  --bmc1_ucm_init_mode                    2
% 3.79/0.98  --bmc1_ucm_cone_mode                    none
% 3.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.98  --bmc1_ucm_relax_model                  4
% 3.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.98  --bmc1_ucm_layered_model                none
% 3.79/0.98  --bmc1_ucm_max_lemma_size               10
% 3.79/0.98  
% 3.79/0.98  ------ AIG Options
% 3.79/0.98  
% 3.79/0.98  --aig_mode                              false
% 3.79/0.98  
% 3.79/0.98  ------ Instantiation Options
% 3.79/0.98  
% 3.79/0.98  --instantiation_flag                    true
% 3.79/0.98  --inst_sos_flag                         true
% 3.79/0.98  --inst_sos_phase                        true
% 3.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.98  --inst_lit_sel_side                     none
% 3.79/0.98  --inst_solver_per_active                1400
% 3.79/0.98  --inst_solver_calls_frac                1.
% 3.79/0.98  --inst_passive_queue_type               priority_queues
% 3.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.98  --inst_passive_queues_freq              [25;2]
% 3.79/0.98  --inst_dismatching                      true
% 3.79/0.98  --inst_eager_unprocessed_to_passive     true
% 3.79/0.98  --inst_prop_sim_given                   true
% 3.79/0.98  --inst_prop_sim_new                     false
% 3.79/0.98  --inst_subs_new                         false
% 3.79/0.98  --inst_eq_res_simp                      false
% 3.79/0.98  --inst_subs_given                       false
% 3.79/0.98  --inst_orphan_elimination               true
% 3.79/0.98  --inst_learning_loop_flag               true
% 3.79/0.98  --inst_learning_start                   3000
% 3.79/0.98  --inst_learning_factor                  2
% 3.79/0.98  --inst_start_prop_sim_after_learn       3
% 3.79/0.98  --inst_sel_renew                        solver
% 3.79/0.98  --inst_lit_activity_flag                true
% 3.79/0.98  --inst_restr_to_given                   false
% 3.79/0.98  --inst_activity_threshold               500
% 3.79/0.98  --inst_out_proof                        true
% 3.79/0.98  
% 3.79/0.98  ------ Resolution Options
% 3.79/0.98  
% 3.79/0.98  --resolution_flag                       false
% 3.79/0.98  --res_lit_sel                           adaptive
% 3.79/0.98  --res_lit_sel_side                      none
% 3.79/0.98  --res_ordering                          kbo
% 3.79/0.98  --res_to_prop_solver                    active
% 3.79/0.98  --res_prop_simpl_new                    false
% 3.79/0.98  --res_prop_simpl_given                  true
% 3.79/0.98  --res_passive_queue_type                priority_queues
% 3.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.98  --res_passive_queues_freq               [15;5]
% 3.79/0.98  --res_forward_subs                      full
% 3.79/0.98  --res_backward_subs                     full
% 3.79/0.98  --res_forward_subs_resolution           true
% 3.79/0.98  --res_backward_subs_resolution          true
% 3.79/0.98  --res_orphan_elimination                true
% 3.79/0.98  --res_time_limit                        2.
% 3.79/0.98  --res_out_proof                         true
% 3.79/0.98  
% 3.79/0.98  ------ Superposition Options
% 3.79/0.98  
% 3.79/0.98  --superposition_flag                    true
% 3.79/0.98  --sup_passive_queue_type                priority_queues
% 3.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.79/0.98  --demod_completeness_check              fast
% 3.79/0.98  --demod_use_ground                      true
% 3.79/0.98  --sup_to_prop_solver                    passive
% 3.79/0.98  --sup_prop_simpl_new                    true
% 3.79/0.98  --sup_prop_simpl_given                  true
% 3.79/0.98  --sup_fun_splitting                     true
% 3.79/0.98  --sup_smt_interval                      50000
% 3.79/0.98  
% 3.79/0.98  ------ Superposition Simplification Setup
% 3.79/0.98  
% 3.79/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.79/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.79/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.79/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.79/0.98  --sup_immed_triv                        [TrivRules]
% 3.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_immed_bw_main                     []
% 3.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.98  --sup_input_bw                          []
% 3.79/0.98  
% 3.79/0.98  ------ Combination Options
% 3.79/0.98  
% 3.79/0.98  --comb_res_mult                         3
% 3.79/0.98  --comb_sup_mult                         2
% 3.79/0.98  --comb_inst_mult                        10
% 3.79/0.98  
% 3.79/0.98  ------ Debug Options
% 3.79/0.98  
% 3.79/0.98  --dbg_backtrace                         false
% 3.79/0.98  --dbg_dump_prop_clauses                 false
% 3.79/0.98  --dbg_dump_prop_clauses_file            -
% 3.79/0.98  --dbg_out_stat                          false
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  ------ Proving...
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  % SZS status Theorem for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  fof(f6,axiom,(
% 3.79/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f24,plain,(
% 3.79/0.98    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.79/0.98    inference(ennf_transformation,[],[f6])).
% 3.79/0.98  
% 3.79/0.98  fof(f25,plain,(
% 3.79/0.98    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.79/0.98    inference(flattening,[],[f24])).
% 3.79/0.98  
% 3.79/0.98  fof(f38,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f25])).
% 3.79/0.98  
% 3.79/0.98  fof(f7,conjecture,(
% 3.79/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)))))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f8,negated_conjecture,(
% 3.79/0.98    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)))))),
% 3.79/0.98    inference(negated_conjecture,[],[f7])).
% 3.79/0.98  
% 3.79/0.98  fof(f26,plain,(
% 3.79/0.98    ? [X0] : (? [X1] : (? [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.79/0.98    inference(ennf_transformation,[],[f8])).
% 3.79/0.98  
% 3.79/0.98  fof(f27,plain,(
% 3.79/0.98    ? [X0] : (? [X1] : (? [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.79/0.98    inference(flattening,[],[f26])).
% 3.79/0.98  
% 3.79/0.98  fof(f30,plain,(
% 3.79/0.98    ( ! [X0,X1] : (? [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,sK2)) != k7_lattices(X0,k3_lattices(X0,X1,sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.79/0.98    introduced(choice_axiom,[])).
% 3.79/0.98  
% 3.79/0.98  fof(f29,plain,(
% 3.79/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k4_lattices(X0,k7_lattices(X0,sK1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 3.79/0.98    introduced(choice_axiom,[])).
% 3.79/0.98  
% 3.79/0.98  fof(f28,plain,(
% 3.79/0.98    ? [X0] : (? [X1] : (? [X2] : (k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) != k7_lattices(X0,k3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X2)) != k7_lattices(sK0,k3_lattices(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.79/0.98    introduced(choice_axiom,[])).
% 3.79/0.98  
% 3.79/0.98  fof(f31,plain,(
% 3.79/0.98    ((k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.79/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 3.79/0.98  
% 3.79/0.98  fof(f41,plain,(
% 3.79/0.98    v17_lattices(sK0)),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f39,plain,(
% 3.79/0.98    ~v2_struct_0(sK0)),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f40,plain,(
% 3.79/0.98    v10_lattices(sK0)),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f42,plain,(
% 3.79/0.98    l3_lattices(sK0)),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f1,axiom,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f10,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f1])).
% 3.79/0.98  
% 3.79/0.98  fof(f11,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.79/0.98  
% 3.79/0.98  fof(f12,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.79/0.98  
% 3.79/0.98  fof(f13,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f12])).
% 3.79/0.98  
% 3.79/0.98  fof(f14,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.79/0.98  
% 3.79/0.98  fof(f15,plain,(
% 3.79/0.98    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.79/0.98    inference(ennf_transformation,[],[f14])).
% 3.79/0.98  
% 3.79/0.98  fof(f16,plain,(
% 3.79/0.98    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.79/0.98    inference(flattening,[],[f15])).
% 3.79/0.98  
% 3.79/0.98  fof(f33,plain,(
% 3.79/0.98    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f16])).
% 3.79/0.98  
% 3.79/0.98  fof(f4,axiom,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f9,plain,(
% 3.79/0.98    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 3.79/0.98    inference(pure_predicate_removal,[],[f4])).
% 3.79/0.98  
% 3.79/0.98  fof(f21,plain,(
% 3.79/0.98    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 3.79/0.98    inference(ennf_transformation,[],[f9])).
% 3.79/0.98  
% 3.79/0.98  fof(f36,plain,(
% 3.79/0.98    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f21])).
% 3.79/0.98  
% 3.79/0.98  fof(f2,axiom,(
% 3.79/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f17,plain,(
% 3.79/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.79/0.98    inference(ennf_transformation,[],[f2])).
% 3.79/0.98  
% 3.79/0.98  fof(f18,plain,(
% 3.79/0.98    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.79/0.98    inference(flattening,[],[f17])).
% 3.79/0.98  
% 3.79/0.98  fof(f34,plain,(
% 3.79/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f18])).
% 3.79/0.98  
% 3.79/0.98  fof(f3,axiom,(
% 3.79/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f19,plain,(
% 3.79/0.98    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.79/0.98    inference(ennf_transformation,[],[f3])).
% 3.79/0.98  
% 3.79/0.98  fof(f20,plain,(
% 3.79/0.98    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.79/0.98    inference(flattening,[],[f19])).
% 3.79/0.98  
% 3.79/0.98  fof(f35,plain,(
% 3.79/0.98    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f20])).
% 3.79/0.98  
% 3.79/0.98  fof(f5,axiom,(
% 3.79/0.98    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 3.79/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.98  
% 3.79/0.98  fof(f22,plain,(
% 3.79/0.98    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.79/0.98    inference(ennf_transformation,[],[f5])).
% 3.79/0.98  
% 3.79/0.98  fof(f23,plain,(
% 3.79/0.98    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.79/0.98    inference(flattening,[],[f22])).
% 3.79/0.98  
% 3.79/0.98  fof(f37,plain,(
% 3.79/0.98    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.79/0.98    inference(cnf_transformation,[],[f23])).
% 3.79/0.98  
% 3.79/0.98  fof(f44,plain,(
% 3.79/0.98    m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f45,plain,(
% 3.79/0.98    k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  fof(f43,plain,(
% 3.79/0.98    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.79/0.98    inference(cnf_transformation,[],[f31])).
% 3.79/0.98  
% 3.79/0.98  cnf(c_350,plain,
% 3.79/0.98      ( X0_42 != X1_42
% 3.79/0.98      | k7_lattices(X0_44,X0_42) = k7_lattices(X0_44,X1_42) ),
% 3.79/0.98      theory(equality) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_493,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) != X0_42
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,X0_42) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_350]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_502,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,X0_42,X1_42)
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,X1_42)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_493]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_995,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_502]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_15362,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) != k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_995]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_6,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | ~ v17_lattices(X1)
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X1)
% 3.79/0.98      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0)) ),
% 3.79/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_11,negated_conjecture,
% 3.79/0.98      ( v17_lattices(sK0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_200,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X1)
% 3.79/0.98      | k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X0)) = k7_lattices(X1,k4_lattices(X1,X2,X0))
% 3.79/0.98      | sK0 != X1 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_201,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.79/0.98      | ~ l3_lattices(sK0)
% 3.79/0.98      | v2_struct_0(sK0)
% 3.79/0.98      | ~ v10_lattices(sK0)
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_200]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_13,negated_conjecture,
% 3.79/0.98      ( ~ v2_struct_0(sK0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_12,negated_conjecture,
% 3.79/0.98      ( v10_lattices(sK0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_10,negated_conjecture,
% 3.79/0.98      ( l3_lattices(sK0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_205,plain,
% 3.79/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 3.79/0.98      inference(global_propositional_subsumption,
% 3.79/0.98                [status(thm)],
% 3.79/0.98                [c_201,c_13,c_12,c_10]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_206,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) = k7_lattices(sK0,k4_lattices(sK0,X0,X1)) ),
% 3.79/0.98      inference(renaming,[status(thm)],[c_205]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_341,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1_42,u1_struct_0(sK0))
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42)) = k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42)) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_206]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_4162,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,X0_42,k7_lattices(sK0,sK2))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_341]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_12459,plain,
% 3.79/0.98      ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.79/0.98      | k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_4162]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_347,plain,
% 3.79/0.98      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 3.79/0.98      theory(equality) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_707,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != X0_42
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X1_42,sK2))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,X1_42,sK2)) != X0_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_11315,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,X0_42,sK2))
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,X0_42,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_707]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_11316,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) != k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_11315]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_351,plain,
% 3.79/0.98      ( X0_42 != X1_42
% 3.79/0.98      | X2_42 != X3_42
% 3.79/0.98      | k3_lattices(X0_44,X0_42,X2_42) = k3_lattices(X0_44,X1_42,X3_42) ),
% 3.79/0.98      theory(equality) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_520,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,X0_42,X1_42)
% 3.79/0.98      | sK2 != X1_42
% 3.79/0.98      | sK1 != X0_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_351]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_987,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,X0_42,k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
% 3.79/0.98      | sK1 != X0_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_520]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_4398,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
% 3.79/0.98      | sK1 != k7_lattices(sK0,X0_42) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_987]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_7121,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,X0_42)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
% 3.79/0.98      | sK1 != k7_lattices(sK0,k7_lattices(sK0,X0_42)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_4398]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_7123,plain,
% 3.79/0.98      ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
% 3.79/0.98      | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
% 3.79/0.98      | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_7121]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1120,plain,
% 3.79/0.98      ( X0_42 != X1_42
% 3.79/0.98      | X0_42 = k7_lattices(sK0,X2_42)
% 3.79/0.98      | k7_lattices(sK0,X2_42) != X1_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1629,plain,
% 3.79/0.98      ( X0_42 != k7_lattices(sK0,X1_42)
% 3.79/0.98      | X0_42 = k7_lattices(sK0,X2_42)
% 3.79/0.98      | k7_lattices(sK0,X2_42) != k7_lattices(sK0,X1_42) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1120]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1776,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,X0_42)
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
% 3.79/0.98      | k7_lattices(sK0,X0_42) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1629]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_5453,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))))
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) != k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1776]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_2483,plain,
% 3.79/0.98      ( X0_42 != k7_lattices(sK0,X1_42)
% 3.79/0.98      | k7_lattices(sK0,X0_42) = k7_lattices(sK0,k7_lattices(sK0,X1_42)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_350]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_4694,plain,
% 3.79/0.98      ( k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42)) != k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,X0_42),k7_lattices(sK0,X1_42))) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,X0_42,X1_42))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_2483]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_5452,plain,
% 3.79/0.98      ( k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) != k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
% 3.79/0.98      | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_4694]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_0,plain,
% 3.79/0.98      ( ~ l3_lattices(X0)
% 3.79/0.98      | v2_struct_0(X0)
% 3.79/0.98      | ~ v10_lattices(X0)
% 3.79/0.98      | v6_lattices(X0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_4,plain,
% 3.79/0.98      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 3.79/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_2,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l1_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v6_lattices(X1) ),
% 3.79/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_138,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X3)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v6_lattices(X1)
% 3.79/0.98      | X1 != X3 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_2]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_139,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v6_lattices(X1) ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_138]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_169,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X3)
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X3)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X3)
% 3.79/0.98      | X1 != X3 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_139]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_170,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X1) ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_169]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_246,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | sK0 != X1 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_170,c_12]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_247,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
% 3.79/0.98      | ~ l3_lattices(sK0)
% 3.79/0.98      | v2_struct_0(sK0) ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_246]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_251,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
% 3.79/0.98      inference(global_propositional_subsumption,
% 3.79/0.98                [status(thm)],
% 3.79/0.98                [c_247,c_13,c_10]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_339,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X1_42,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k4_lattices(sK0,X0_42,X1_42),u1_struct_0(sK0)) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_251]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_2233,plain,
% 3.79/0.98      ( m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_339]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_3,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1) ),
% 3.79/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_271,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | sK0 != X1 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_272,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 3.79/0.98      | ~ l3_lattices(sK0) ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_271]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_276,plain,
% 3.79/0.98      ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(global_propositional_subsumption,
% 3.79/0.98                [status(thm)],
% 3.79/0.98                [c_272,c_10]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_277,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
% 3.79/0.98      inference(renaming,[status(thm)],[c_276]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_338,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
% 3.79/0.98      | m1_subset_1(k7_lattices(sK0,X0_42),u1_struct_0(sK0)) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_277]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_2206,plain,
% 3.79/0.98      ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_338]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1615,plain,
% 3.79/0.98      ( X0_42 != X1_42
% 3.79/0.98      | X0_42 = k7_lattices(sK0,k7_lattices(sK0,X1_42))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,X1_42)) != X1_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1120]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1616,plain,
% 3.79/0.98      ( k7_lattices(sK0,k7_lattices(sK0,sK1)) != sK1
% 3.79/0.98      | sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
% 3.79/0.98      | sK1 != sK1 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1615]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_5,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ v17_lattices(X1)
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X1)
% 3.79/0.98      | k7_lattices(X1,k7_lattices(X1,X0)) = X0 ),
% 3.79/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_221,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.79/0.98      | ~ l3_lattices(X1)
% 3.79/0.98      | v2_struct_0(X1)
% 3.79/0.98      | ~ v10_lattices(X1)
% 3.79/0.98      | k7_lattices(X1,k7_lattices(X1,X0)) = X0
% 3.79/0.98      | sK0 != X1 ),
% 3.79/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_222,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | ~ l3_lattices(sK0)
% 3.79/0.98      | v2_struct_0(sK0)
% 3.79/0.98      | ~ v10_lattices(sK0)
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
% 3.79/0.98      inference(unflattening,[status(thm)],[c_221]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_226,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0)) = X0 ),
% 3.79/0.98      inference(global_propositional_subsumption,
% 3.79/0.98                [status(thm)],
% 3.79/0.98                [c_222,c_13,c_12,c_10]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_340,plain,
% 3.79/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK0))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,X0_42)) = X0_42 ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_226]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1425,plain,
% 3.79/0.98      ( ~ m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),u1_struct_0(sK0))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_340]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_818,plain,
% 3.79/0.98      ( X0_42 != X1_42
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != X1_42
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = X0_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1041,plain,
% 3.79/0.98      ( X0_42 != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = X0_42
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_818]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1424,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
% 3.79/0.98      | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_1041]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_346,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_1038,plain,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_346]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_559,plain,
% 3.79/0.98      ( X0_42 != X1_42 | sK2 != X1_42 | sK2 = X0_42 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_639,plain,
% 3.79/0.98      ( X0_42 != sK2 | sK2 = X0_42 | sK2 != sK2 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_559]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_852,plain,
% 3.79/0.98      ( k7_lattices(sK0,k7_lattices(sK0,sK2)) != sK2
% 3.79/0.98      | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
% 3.79/0.98      | sK2 != sK2 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_639]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_729,plain,
% 3.79/0.98      ( sK2 = sK2 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_346]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_8,negated_conjecture,
% 3.79/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_343,negated_conjecture,
% 3.79/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_466,plain,
% 3.79/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.79/0.98      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_469,plain,
% 3.79/0.98      ( k7_lattices(sK0,k7_lattices(sK0,X0_42)) = X0_42
% 3.79/0.98      | m1_subset_1(X0_42,u1_struct_0(sK0)) != iProver_top ),
% 3.79/0.98      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_524,plain,
% 3.79/0.98      ( k7_lattices(sK0,k7_lattices(sK0,sK2)) = sK2 ),
% 3.79/0.98      inference(superposition,[status(thm)],[c_466,c_469]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_370,plain,
% 3.79/0.98      ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
% 3.79/0.98      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_338]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_364,plain,
% 3.79/0.98      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.79/0.98      | k7_lattices(sK0,k7_lattices(sK0,sK1)) = sK1 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_340]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_7,negated_conjecture,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
% 3.79/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_344,negated_conjecture,
% 3.79/0.98      ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) ),
% 3.79/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_357,plain,
% 3.79/0.98      ( sK1 = sK1 ),
% 3.79/0.98      inference(instantiation,[status(thm)],[c_346]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(c_9,negated_conjecture,
% 3.79/0.98      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.79/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.79/0.98  
% 3.79/0.98  cnf(contradiction,plain,
% 3.79/0.98      ( $false ),
% 3.79/0.98      inference(minisat,
% 3.79/0.98                [status(thm)],
% 3.79/0.98                [c_15362,c_12459,c_11316,c_7123,c_5453,c_5452,c_2233,
% 3.79/0.98                 c_2206,c_1616,c_1425,c_1424,c_1038,c_852,c_729,c_524,
% 3.79/0.98                 c_370,c_364,c_344,c_357,c_8,c_9]) ).
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.98  
% 3.79/0.98  ------                               Statistics
% 3.79/0.98  
% 3.79/0.98  ------ General
% 3.79/0.98  
% 3.79/0.98  abstr_ref_over_cycles:                  0
% 3.79/0.98  abstr_ref_under_cycles:                 0
% 3.79/0.98  gc_basic_clause_elim:                   0
% 3.79/0.98  forced_gc_time:                         0
% 3.79/0.98  parsing_time:                           0.009
% 3.79/0.98  unif_index_cands_time:                  0.
% 3.79/0.98  unif_index_add_time:                    0.
% 3.79/0.98  orderings_time:                         0.
% 3.79/0.98  out_proof_time:                         0.01
% 3.79/0.98  total_time:                             0.466
% 3.79/0.98  num_of_symbols:                         45
% 3.79/0.98  num_of_terms:                           11645
% 3.79/0.98  
% 3.79/0.98  ------ Preprocessing
% 3.79/0.98  
% 3.79/0.98  num_of_splits:                          0
% 3.79/0.98  num_of_split_atoms:                     0
% 3.79/0.98  num_of_reused_defs:                     0
% 3.79/0.98  num_eq_ax_congr_red:                    7
% 3.79/0.98  num_of_sem_filtered_clauses:            1
% 3.79/0.98  num_of_subtypes:                        3
% 3.79/0.98  monotx_restored_types:                  0
% 3.79/0.98  sat_num_of_epr_types:                   0
% 3.79/0.98  sat_num_of_non_cyclic_types:            0
% 3.79/0.98  sat_guarded_non_collapsed_types:        1
% 3.79/0.98  num_pure_diseq_elim:                    0
% 3.79/0.98  simp_replaced_by:                       0
% 3.79/0.98  res_preprocessed:                       47
% 3.79/0.98  prep_upred:                             0
% 3.79/0.98  prep_unflattend:                        6
% 3.79/0.98  smt_new_axioms:                         0
% 3.79/0.98  pred_elim_cands:                        1
% 3.79/0.98  pred_elim:                              6
% 3.79/0.98  pred_elim_cl:                           6
% 3.79/0.98  pred_elim_cycles:                       8
% 3.79/0.98  merged_defs:                            0
% 3.79/0.98  merged_defs_ncl:                        0
% 3.79/0.98  bin_hyper_res:                          0
% 3.79/0.98  prep_cycles:                            4
% 3.79/0.98  pred_elim_time:                         0.003
% 3.79/0.98  splitting_time:                         0.
% 3.79/0.98  sem_filter_time:                        0.
% 3.79/0.98  monotx_time:                            0.
% 3.79/0.98  subtype_inf_time:                       0.
% 3.79/0.98  
% 3.79/0.98  ------ Problem properties
% 3.79/0.98  
% 3.79/0.98  clauses:                                7
% 3.79/0.98  conjectures:                            3
% 3.79/0.98  epr:                                    0
% 3.79/0.98  horn:                                   7
% 3.79/0.98  ground:                                 3
% 3.79/0.98  unary:                                  3
% 3.79/0.98  binary:                                 2
% 3.79/0.98  lits:                                   13
% 3.79/0.98  lits_eq:                                3
% 3.79/0.98  fd_pure:                                0
% 3.79/0.98  fd_pseudo:                              0
% 3.79/0.98  fd_cond:                                0
% 3.79/0.98  fd_pseudo_cond:                         0
% 3.79/0.98  ac_symbols:                             0
% 3.79/0.98  
% 3.79/0.98  ------ Propositional Solver
% 3.79/0.98  
% 3.79/0.98  prop_solver_calls:                      38
% 3.79/0.98  prop_fast_solver_calls:                 496
% 3.79/0.98  smt_solver_calls:                       0
% 3.79/0.98  smt_fast_solver_calls:                  0
% 3.79/0.98  prop_num_of_clauses:                    3676
% 3.79/0.98  prop_preprocess_simplified:             6147
% 3.79/0.98  prop_fo_subsumed:                       18
% 3.79/0.98  prop_solver_time:                       0.
% 3.79/0.98  smt_solver_time:                        0.
% 3.79/0.98  smt_fast_solver_time:                   0.
% 3.79/0.98  prop_fast_solver_time:                  0.
% 3.79/0.98  prop_unsat_core_time:                   0.
% 3.79/0.98  
% 3.79/0.98  ------ QBF
% 3.79/0.98  
% 3.79/0.98  qbf_q_res:                              0
% 3.79/0.98  qbf_num_tautologies:                    0
% 3.79/0.98  qbf_prep_cycles:                        0
% 3.79/0.98  
% 3.79/0.98  ------ BMC1
% 3.79/0.98  
% 3.79/0.98  bmc1_current_bound:                     -1
% 3.79/0.98  bmc1_last_solved_bound:                 -1
% 3.79/0.98  bmc1_unsat_core_size:                   -1
% 3.79/0.98  bmc1_unsat_core_parents_size:           -1
% 3.79/0.98  bmc1_merge_next_fun:                    0
% 3.79/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.79/0.98  
% 3.79/0.98  ------ Instantiation
% 3.79/0.98  
% 3.79/0.98  inst_num_of_clauses:                    1507
% 3.79/0.98  inst_num_in_passive:                    523
% 3.79/0.98  inst_num_in_active:                     690
% 3.79/0.98  inst_num_in_unprocessed:                294
% 3.79/0.98  inst_num_of_loops:                      785
% 3.79/0.98  inst_num_of_learning_restarts:          0
% 3.79/0.98  inst_num_moves_active_passive:          84
% 3.79/0.98  inst_lit_activity:                      0
% 3.79/0.98  inst_lit_activity_moves:                0
% 3.79/0.98  inst_num_tautologies:                   0
% 3.79/0.98  inst_num_prop_implied:                  0
% 3.79/0.98  inst_num_existing_simplified:           0
% 3.79/0.98  inst_num_eq_res_simplified:             0
% 3.79/0.98  inst_num_child_elim:                    0
% 3.79/0.98  inst_num_of_dismatching_blockings:      4108
% 3.79/0.98  inst_num_of_non_proper_insts:           4117
% 3.79/0.98  inst_num_of_duplicates:                 0
% 3.79/0.98  inst_inst_num_from_inst_to_res:         0
% 3.79/0.98  inst_dismatching_checking_time:         0.
% 3.79/0.98  
% 3.79/0.98  ------ Resolution
% 3.79/0.98  
% 3.79/0.98  res_num_of_clauses:                     0
% 3.79/0.98  res_num_in_passive:                     0
% 3.79/0.98  res_num_in_active:                      0
% 3.79/0.98  res_num_of_loops:                       51
% 3.79/0.98  res_forward_subset_subsumed:            194
% 3.79/0.98  res_backward_subset_subsumed:           2
% 3.79/0.98  res_forward_subsumed:                   0
% 3.79/0.98  res_backward_subsumed:                  0
% 3.79/0.98  res_forward_subsumption_resolution:     0
% 3.79/0.98  res_backward_subsumption_resolution:    0
% 3.79/0.98  res_clause_to_clause_subsumption:       1334
% 3.79/0.98  res_orphan_elimination:                 0
% 3.79/0.98  res_tautology_del:                      575
% 3.79/0.98  res_num_eq_res_simplified:              0
% 3.79/0.98  res_num_sel_changes:                    0
% 3.79/0.98  res_moves_from_active_to_pass:          0
% 3.79/0.98  
% 3.79/0.98  ------ Superposition
% 3.79/0.98  
% 3.79/0.98  sup_time_total:                         0.
% 3.79/0.98  sup_time_generating:                    0.
% 3.79/0.98  sup_time_sim_full:                      0.
% 3.79/0.98  sup_time_sim_immed:                     0.
% 3.79/0.98  
% 3.79/0.98  sup_num_of_clauses:                     479
% 3.79/0.98  sup_num_in_active:                      151
% 3.79/0.98  sup_num_in_passive:                     328
% 3.79/0.98  sup_num_of_loops:                       156
% 3.79/0.98  sup_fw_superposition:                   291
% 3.79/0.98  sup_bw_superposition:                   306
% 3.79/0.98  sup_immediate_simplified:               230
% 3.79/0.98  sup_given_eliminated:                   0
% 3.79/0.98  comparisons_done:                       0
% 3.79/0.98  comparisons_avoided:                    0
% 3.79/0.98  
% 3.79/0.98  ------ Simplifications
% 3.79/0.98  
% 3.79/0.98  
% 3.79/0.98  sim_fw_subset_subsumed:                 5
% 3.79/0.98  sim_bw_subset_subsumed:                 8
% 3.79/0.98  sim_fw_subsumed:                        0
% 3.79/0.98  sim_bw_subsumed:                        0
% 3.79/0.98  sim_fw_subsumption_res:                 0
% 3.79/0.98  sim_bw_subsumption_res:                 0
% 3.79/0.98  sim_tautology_del:                      3
% 3.79/0.98  sim_eq_tautology_del:                   97
% 3.79/0.98  sim_eq_res_simp:                        0
% 3.79/0.98  sim_fw_demodulated:                     39
% 3.79/0.98  sim_bw_demodulated:                     0
% 3.79/0.98  sim_light_normalised:                   186
% 3.79/0.98  sim_joinable_taut:                      0
% 3.79/0.98  sim_joinable_simp:                      0
% 3.79/0.98  sim_ac_normalised:                      0
% 3.79/0.98  sim_smt_subsumption:                    0
% 3.79/0.98  
%------------------------------------------------------------------------------
