%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1217+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:10 EST 2020

% Result     : Theorem 35.71s
% Output     : CNFRefutation 35.71s
% Verified   : 
% Statistics : Number of formulae       :  272 (2792 expanded)
%              Number of clauses        :  189 ( 683 expanded)
%              Number of leaves         :   21 ( 836 expanded)
%              Depth                    :   27
%              Number of atoms          : 1222 (18478 expanded)
%              Number of equality atoms :  245 ( 438 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK3),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK2))
            & r3_lattices(X0,sK2,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
              ( ~ r3_lattices(sK1,k7_lattices(sK1,X2),k7_lattices(sK1,X1))
              & r3_lattices(sK1,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v17_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2))
    & r3_lattices(sK1,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v17_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f53,f60,f59,f58])).

fof(f93,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f63,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1355,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1790,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_798,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k7_lattices(sK1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_802,plain,
    ( m1_subset_1(k7_lattices(sK1,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_33])).

cnf(c_803,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k7_lattices(sK1,X0),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_802])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | m1_subset_1(k7_lattices(sK1,X0_53),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_803])).

cnf(c_1794,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_lattices(sK1,X0_53),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1354,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1791,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1354])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_656,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_32])).

cnf(c_657,plain,
    ( v6_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_103,plain,
    ( v6_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_659,plain,
    ( v6_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_33,c_32,c_30,c_103])).

cnf(c_820,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_659])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k2_lattices(sK1,X1,X0) = k4_lattices(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_15,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_73,plain,
    ( l1_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_lattices(sK1,X1,X0) = k4_lattices(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_33,c_30,c_73])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k2_lattices(sK1,X0,X1) = k4_lattices(sK1,X0,X1) ),
    inference(renaming,[status(thm)],[c_825])).

cnf(c_1350,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | k2_lattices(sK1,X0_53,X1_53) = k4_lattices(sK1,X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_826])).

cnf(c_1795,plain,
    ( k2_lattices(sK1,X0_53,X1_53) = k4_lattices(sK1,X0_53,X1_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_2163,plain,
    ( k2_lattices(sK1,sK2,X0_53) = k4_lattices(sK1,sK2,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1795])).

cnf(c_2301,plain,
    ( k2_lattices(sK1,sK2,k7_lattices(sK1,X0_53)) = k4_lattices(sK1,sK2,k7_lattices(sK1,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_2163])).

cnf(c_4028,plain,
    ( k2_lattices(sK1,sK2,k7_lattices(sK1,sK3)) = k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_1790,c_2301])).

cnf(c_2162,plain,
    ( k2_lattices(sK1,sK3,X0_53) = k4_lattices(sK1,sK3,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1795])).

cnf(c_2179,plain,
    ( k2_lattices(sK1,sK3,k7_lattices(sK1,X0_53)) = k4_lattices(sK1,sK3,k7_lattices(sK1,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_2162])).

cnf(c_3814,plain,
    ( k2_lattices(sK1,sK3,k7_lattices(sK1,sK3)) = k4_lattices(sK1,sK3,k7_lattices(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_1790,c_2179])).

cnf(c_2,plain,
    ( v7_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v7_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_479,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_483,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_22,c_2,c_1,c_0])).

cnf(c_484,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_602,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_484,c_32])).

cnf(c_603,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_607,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_33,c_30])).

cnf(c_608,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | r1_lattices(sK1,k2_lattices(sK1,X0,X2),k2_lattices(sK1,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_607])).

cnf(c_1353,plain,
    ( ~ r1_lattices(sK1,X0_53,X1_53)
    | r1_lattices(sK1,k2_lattices(sK1,X0_53,X2_53),k2_lattices(sK1,X1_53,X2_53))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_53,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_1792,plain,
    ( r1_lattices(sK1,X0_53,X1_53) != iProver_top
    | r1_lattices(sK1,k2_lattices(sK1,X0_53,X2_53),k2_lattices(sK1,X1_53,X2_53)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_53,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_3909,plain,
    ( r1_lattices(sK1,X0_53,sK3) != iProver_top
    | r1_lattices(sK1,k2_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_1792])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1870,plain,
    ( m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1871,plain,
    ( m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_133720,plain,
    ( r1_lattices(sK1,X0_53,sK3) != iProver_top
    | r1_lattices(sK1,k2_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),k4_lattices(sK1,sK3,k7_lattices(sK1,sK3))) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3909,c_39,c_1871])).

cnf(c_24,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_565,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_566,plain,
    ( ~ r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | k4_lattices(sK1,X0,X1) = k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | k4_lattices(sK1,X0,X1) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_33,c_32,c_30])).

cnf(c_571,plain,
    ( ~ r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k4_lattices(sK1,X0,X1) = k5_lattices(sK1) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_20,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_678,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_32])).

cnf(c_679,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | v9_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_112,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | v9_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_681,plain,
    ( v9_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_33,c_32,c_30,c_112])).

cnf(c_707,plain,
    ( r3_lattices(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_681])).

cnf(c_708,plain,
    ( r3_lattices(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v6_lattices(sK1)
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_109,plain,
    ( v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_712,plain,
    ( r3_lattices(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_33,c_32,c_30,c_103,c_109])).

cnf(c_713,plain,
    ( r3_lattices(sK1,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | X2 != X1
    | k4_lattices(sK1,X1,X0) = k5_lattices(sK1)
    | k7_lattices(sK1,X0) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_713])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,X0),u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,X0),X0) = k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_1056])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,X0),X0) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1057,c_33,c_798])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,X1),X1) = k5_lattices(sK1) ),
    inference(renaming,[status(thm)],[c_1061])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,X1_53),X1_53) = k5_lattices(sK1) ),
    inference(subtyping,[status(esa)],[c_1062])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) = k5_lattices(sK1)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1338])).

cnf(c_1810,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) = k5_lattices(sK1)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( ~ r3_lattices(sK1,k7_lattices(sK1,sK3),k7_lattices(sK1,sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_960,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k7_lattices(sK1,sK2) != X1
    | k7_lattices(sK1,sK3) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_713])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | k7_lattices(sK1,sK3) != k7_lattices(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_960])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | k7_lattices(sK1,sK3) != k7_lattices(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_961])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1344])).

cnf(c_1405,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_1407,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_1360,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1338])).

cnf(c_1419,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_1421,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) = k5_lattices(sK1)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_7781,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) = k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1810,c_38,c_1407,c_1419,c_1421])).

cnf(c_7782,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) = k5_lattices(sK1)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7781])).

cnf(c_7785,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,sK3),sK3) = k5_lattices(sK1) ),
    inference(superposition,[status(thm)],[c_1790,c_7782])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_659])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1)
    | k4_lattices(sK1,X1,X0) = k4_lattices(sK1,X0,X1) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_867,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k4_lattices(sK1,X1,X0) = k4_lattices(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_863,c_33,c_30,c_73])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k4_lattices(sK1,X0,X1) = k4_lattices(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_867])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | k4_lattices(sK1,X0_53,X1_53) = k4_lattices(sK1,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_868])).

cnf(c_1797,plain,
    ( k4_lattices(sK1,X0_53,X1_53) = k4_lattices(sK1,X1_53,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1348])).

cnf(c_4183,plain,
    ( k4_lattices(sK1,X0_53,sK3) = k4_lattices(sK1,sK3,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1797])).

cnf(c_4566,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),sK3) = k4_lattices(sK1,sK3,k7_lattices(sK1,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_4183])).

cnf(c_6811,plain,
    ( k4_lattices(sK1,sK3,k7_lattices(sK1,sK3)) = k4_lattices(sK1,k7_lattices(sK1,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1790,c_4566])).

cnf(c_7802,plain,
    ( k4_lattices(sK1,sK3,k7_lattices(sK1,sK3)) = k5_lattices(sK1) ),
    inference(demodulation,[status(thm)],[c_7785,c_6811])).

cnf(c_133726,plain,
    ( r1_lattices(sK1,X0_53,sK3) != iProver_top
    | r1_lattices(sK1,k2_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),k5_lattices(sK1)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_133720,c_7802])).

cnf(c_133731,plain,
    ( r1_lattices(sK1,k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1)) = iProver_top
    | r1_lattices(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_133726])).

cnf(c_8,plain,
    ( ~ v17_lattices(X0)
    | v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6,plain,
    ( ~ v15_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_351,plain,
    ( ~ v17_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_23,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_373,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_351,c_23])).

cnf(c_523,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_373,c_31])).

cnf(c_524,plain,
    ( r3_lattices(sK1,k5_lattices(sK1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r3_lattices(sK1,k5_lattices(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_33,c_32,c_30])).

cnf(c_529,plain,
    ( r3_lattices(sK1,k5_lattices(sK1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_19,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_728,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_681])).

cnf(c_729,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v6_lattices(sK1)
    | ~ v8_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_733,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_33,c_32,c_30,c_103,c_109])).

cnf(c_734,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_733])).

cnf(c_1041,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 != X2
    | k5_lattices(sK1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_734])).

cnf(c_1042,plain,
    ( r1_lattices(sK1,k5_lattices(sK1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1041])).

cnf(c_1339,plain,
    ( r1_lattices(sK1,k5_lattices(sK1),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1042])).

cnf(c_123892,plain,
    ( r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)))
    | ~ m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_123897,plain,
    ( r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3))) = iProver_top
    | m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123892])).

cnf(c_123899,plain,
    ( r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))) = iProver_top
    | m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_123897])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_403,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_14,c_21])).

cnf(c_441,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_4,c_403])).

cnf(c_629,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_441,c_32])).

cnf(c_630,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_33,c_30])).

cnf(c_635,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_1352,plain,
    ( ~ r1_lattices(sK1,X0_53,X1_53)
    | ~ r1_lattices(sK1,X1_53,X0_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | X1_53 = X0_53 ),
    inference(subtyping,[status(esa)],[c_635])).

cnf(c_1908,plain,
    ( ~ r1_lattices(sK1,k4_lattices(sK1,X0_53,X1_53),k5_lattices(sK1))
    | ~ r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,X1_53))
    | ~ m1_subset_1(k4_lattices(sK1,X0_53,X1_53),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k4_lattices(sK1,X0_53,X1_53) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_28721,plain,
    ( ~ r1_lattices(sK1,k4_lattices(sK1,X0_53,k7_lattices(sK1,X1_53)),k5_lattices(sK1))
    | ~ r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,k7_lattices(sK1,X1_53)))
    | ~ m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,X1_53)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k4_lattices(sK1,X0_53,k7_lattices(sK1,X1_53)) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_71673,plain,
    ( ~ r1_lattices(sK1,k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),k5_lattices(sK1))
    | ~ r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)))
    | ~ m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_28721])).

cnf(c_71674,plain,
    ( k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)) = k5_lattices(sK1)
    | r1_lattices(sK1,k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),k5_lattices(sK1)) != iProver_top
    | r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3))) != iProver_top
    | m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71673])).

cnf(c_71676,plain,
    ( k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) = k5_lattices(sK1)
    | r1_lattices(sK1,k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),k5_lattices(sK1)) != iProver_top
    | r1_lattices(sK1,k5_lattices(sK1),k4_lattices(sK1,sK2,k7_lattices(sK1,sK3))) != iProver_top
    | m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71674])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_659])).

cnf(c_842,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,X1,X0),u1_struct_0(sK1))
    | ~ l1_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_846,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,X1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_33,c_30,c_73])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_846])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,X0_53,X1_53),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_847])).

cnf(c_67774,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_67775,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_lattices(sK1,X0_53,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67774])).

cnf(c_67777,plain,
    ( m1_subset_1(k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_67775])).

cnf(c_4184,plain,
    ( k4_lattices(sK1,X0_53,sK2) = k4_lattices(sK1,sK2,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1797])).

cnf(c_4669,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),sK2) = k4_lattices(sK1,sK2,k7_lattices(sK1,X0_53))
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_4184])).

cnf(c_7046,plain,
    ( k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) = k4_lattices(sK1,k7_lattices(sK1,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_1790,c_4669])).

cnf(c_25,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_541,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_542,plain,
    ( r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1)
    | k4_lattices(sK1,X0,X1) != k5_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | k4_lattices(sK1,X0,X1) != k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_33,c_32,c_30])).

cnf(c_547,plain,
    ( r3_lattices(sK1,X0,k7_lattices(sK1,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k4_lattices(sK1,X0,X1) != k5_lattices(sK1) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_942,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | k4_lattices(sK1,X1,X0) != k5_lattices(sK1)
    | k7_lattices(sK1,X0) != k7_lattices(sK1,sK2)
    | k7_lattices(sK1,sK3) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_547])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,sK3),X0) != k5_lattices(sK1)
    | k7_lattices(sK1,X0) != k7_lattices(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1))
    | k4_lattices(sK1,k7_lattices(sK1,sK3),X0_53) != k5_lattices(sK1)
    | k7_lattices(sK1,X0_53) != k7_lattices(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_943])).

cnf(c_1800,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,sK3),X0_53) != k5_lattices(sK1)
    | k7_lattices(sK1,X0_53) != k7_lattices(sK1,sK2)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1345])).

cnf(c_1401,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,sK3),X0_53) != k5_lattices(sK1)
    | k7_lattices(sK1,X0_53) != k7_lattices(sK1,sK2)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_lattices(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1345])).

cnf(c_2095,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | k7_lattices(sK1,X0_53) != k7_lattices(sK1,sK2)
    | k4_lattices(sK1,k7_lattices(sK1,sK3),X0_53) != k5_lattices(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1800,c_39,c_1401,c_1871])).

cnf(c_2096,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,sK3),X0_53) != k5_lattices(sK1)
    | k7_lattices(sK1,X0_53) != k7_lattices(sK1,sK2)
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2095])).

cnf(c_7630,plain,
    ( k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) != k5_lattices(sK1)
    | k7_lattices(sK1,sK2) != k7_lattices(sK1,sK2)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_2096])).

cnf(c_7631,plain,
    ( k4_lattices(sK1,sK2,k7_lattices(sK1,sK3)) != k5_lattices(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7630])).

cnf(c_2840,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53),u1_struct_0(sK1))
    | ~ m1_subset_1(k7_lattices(sK1,X0_53),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_2841,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k7_lattices(sK1,X0_53),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2840])).

cnf(c_2843,plain,
    ( m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,sK2),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0_53,X0_55)
    | m1_subset_1(X1_53,X0_55)
    | X1_53 != X0_53 ),
    theory(equality)).

cnf(c_1892,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k5_lattices(sK1) != X0_53 ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_2441,plain,
    ( ~ m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53),u1_struct_0(sK1))
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1))
    | k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_2444,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53)
    | m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_2446,plain,
    ( k5_lattices(sK1) != k4_lattices(sK1,k7_lattices(sK1,sK2),sK2)
    | m1_subset_1(k4_lattices(sK1,k7_lattices(sK1,sK2),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k5_lattices(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_1365,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1948,plain,
    ( X0_53 != X1_53
    | k5_lattices(sK1) != X1_53
    | k5_lattices(sK1) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2016,plain,
    ( X0_53 != k5_lattices(sK1)
    | k5_lattices(sK1) = X0_53
    | k5_lattices(sK1) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_2306,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53) != k5_lattices(sK1)
    | k5_lattices(sK1) = k4_lattices(sK1,k7_lattices(sK1,X0_53),X0_53)
    | k5_lattices(sK1) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_2307,plain,
    ( k4_lattices(sK1,k7_lattices(sK1,sK2),sK2) != k5_lattices(sK1)
    | k5_lattices(sK1) = k4_lattices(sK1,k7_lattices(sK1,sK2),sK2)
    | k5_lattices(sK1) != k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_2306])).

cnf(c_1364,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2124,plain,
    ( k5_lattices(sK1) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP1_iProver_split
    | k4_lattices(sK1,k7_lattices(sK1,sK2),sK2) = k5_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_1385,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_lattices(sK1,X0_53),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_1387,plain,
    ( m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_27,negated_conjecture,
    ( r3_lattices(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1009,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_734])).

cnf(c_1010,plain,
    ( r1_lattices(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_1011,plain,
    ( r1_lattices(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_133731,c_123899,c_71676,c_67777,c_7631,c_2843,c_2446,c_2307,c_2124,c_1871,c_1422,c_1360,c_1406,c_1387,c_1011,c_39,c_38,c_29])).


%------------------------------------------------------------------------------
